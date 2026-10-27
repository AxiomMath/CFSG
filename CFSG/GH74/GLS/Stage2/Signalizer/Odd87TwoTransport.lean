module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecTransport

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.Blueprint
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Inj

variable {A : Type} [Group A] [Finite A]

theorem layerHom_ker_iff (a : A) :
    layerHom A a = 1 ↔ a ∈ centralizer ((layer A : Subgroup A) : Set A) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have := congrArg (fun σ : MulAut ↥(layer A) => ((σ ⟨k, hk⟩ : ↥(layer A)) : A)) h
    simp only [layerHom_apply, MulAut.one_apply] at this
    calc k * a = (a * k * a⁻¹) * a := by rw [this]
      _ = a * k := by group
  · intro h
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [layerHom_apply, MulAut.one_apply]
    have := h x x.2
    calc a * (x : A) * a⁻¹ = (x * a) * a⁻¹ := by rw [← this]
      _ = x := by group

omit [Finite A] in
theorem mem_normalizer_of_both {S : Subgroup A} {g : A} (h1 : ∀ x ∈ S, g * x * g⁻¹ ∈ S)
    (h2 : ∀ x ∈ S, g⁻¹ * x * g ∈ S) : g ∈ normalizer (S : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact h1 h
  · intro hg
    have := h2 _ hg
    simpa [mul_assoc] using this

theorem X_inf_ker_eq_bot {zb : A} {p : ℕ} {X : Subgroup A} (hd : CellData zb p X) :
    X ⊓ (layerHom A).ker = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hd.A4.prime⟩
  set X₁ : Subgroup A := X ⊓ (layerHom A).ker with hX₁
  have hzN : zb ∈ normalizer (X : Set A) := z_mem_normalizer_of_sig4A hd.A4
  have hKle : layer A ≤ normalizer (X₁ : Set A) := by
    intro g hg
    have hc : ∀ x ∈ X₁, g * x * g⁻¹ = x := by
      intro x hx
      have hx' : x ∈ centralizer ((layer A : Subgroup A) : Set A) :=
        (layerHom_ker_iff x).mp hx.2
      have := Subgroup.mem_centralizer_iff.mp hx' g hg
      calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [this]
        _ = x := by group
    refine mem_normalizer_of_both (fun x hx => ?_) (fun x hx => ?_)
    · rw [hc x hx]; exact hx
    · have := hc x hx
      have hc' : ∀ x ∈ X₁, g⁻¹ * x * g = x := by
        intro y hy
        have hy' : y ∈ centralizer ((layer A : Subgroup A) : Set A) := (layerHom_ker_iff y).mp hy.2
        have := Subgroup.mem_centralizer_iff.mp hy' g⁻¹ ((layer A).inv_mem hg)
        calc g⁻¹ * y * g = (y * g⁻¹) * g := by rw [this]
          _ = y := by group
      rw [hc' x hx]; exact hx
  have hXle : X ≤ normalizer (X₁ : Set A) := by
    intro g hg
    refine mem_normalizer_of_both (fun x hx => ?_) (fun x hx => ?_)
    · exact ⟨X.mul_mem (X.mul_mem hg hx.1) (X.inv_mem hg), (layerHom A).normal_ker.conj_mem x hx.2 g⟩
    · exact ⟨X.mul_mem (X.mul_mem (X.inv_mem hg) hx.1) (by simpa using hg),
        by simpa using (layerHom A).normal_ker.conj_mem x hx.2 g⁻¹⟩
  have hzle : zpowers zb ≤ normalizer (X₁ : Set A) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_both (fun x hx => ?_) (fun x hx => ?_)
    · exact ⟨(Subgroup.mem_normalizer_iff.mp hzN x).mp hx.1,
        (layerHom A).normal_ker.conj_mem x hx.2 zb⟩
    · have hzN' : zb⁻¹ ∈ normalizer (X : Set A) := (normalizer (X : Set A)).inv_mem hzN
      have h1 := (Subgroup.mem_normalizer_iff.mp hzN' x).mp hx.1
      exact ⟨by simpa using h1, by simpa using (layerHom A).normal_ker.conj_mem x hx.2 zb⁻¹⟩
  have htop : normalizer (X₁ : Set A) = ⊤ := by
    rw [eq_top_iff, ← hd.gen]
    exact sup_le (sup_le hKle hXle) hzle
  have hnorm : X₁.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hp : IsPGroup p ↥X₁ := hd.A4.pgroup.of_injective (Subgroup.inclusion (inf_le_left : X₁ ≤ X)) 
    (Subgroup.inclusion_injective _)
  have hle : X₁ ≤ CFSG.pCore p A := le_sSup ⟨hnorm, hp⟩
  exact le_bot_iff.mp (hd.op ▸ hle)


theorem map_layer_layerHom : (layer A).map (layerHom A) = innSub ↥(layer A) := by
  ext σ
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, (layerHom_coe ⟨a, ha⟩).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, layerHom_coe k⟩

theorem layerHom_injective_of_aut {zb : A} {p : ℕ} {X : Subgroup A} (hd : CellData zb p X)
    (hZ : center ↥(layer A) = ⊥) (hXI : X.map (layerHom A) ⊓ innSub ↥(layer A) = ⊥)
    (hα : layerAut zb ∉ innSub ↥(layer A) ⊔ X.map (layerHom A)) : Function.Injective (layerHom A) := by
  classical
  rw [injective_iff_map_eq_one]
  intro a ha
  have hKn : (layer A).Normal := layer_normal
  have hKker : ∀ k ∈ layer A, layerHom A k = 1 → k = 1 := by
    intro k hk h1
    have hk' : k ∈ centralizer ((layer A : Subgroup A) : Set A) := (layerHom_ker_iff k).mp h1
    have : (⟨k, hk⟩ : ↥(layer A)) ∈ center ↥(layer A) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hk' g g.2
    rw [hZ, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hXker : ∀ x ∈ X, layerHom A x = 1 → x = 1 := by
    intro x hx h1
    have : x ∈ X ⊓ (layerHom A).ker := ⟨hx, h1⟩
    rw [X_inf_ker_eq_bot hd] at this
    exact Subgroup.mem_bot.mp this
  have hzN : zb ∈ normalizer (X : Set A) := z_mem_normalizer_of_sig4A hd.A4
  have hN : (layer A ⊔ X).Normal := normal_sup_of_gen hd.gen hzN
  have hatop : a ∈ zpowers zb ⊔ (layer A ⊔ X) := by
    have : zpowers zb ⊔ (layer A ⊔ X) = ⊤ := by rw [sup_comm, hd.gen]
    rw [this]; exact Subgroup.mem_top a
  rw [← SetLike.mem_coe, Subgroup.mul_normal (zpowers zb) (layer A ⊔ X)] at hatop
  obtain ⟨w, hw, n, hn, rfl⟩ := hatop
  have hn' : n ∈ X ⊔ layer A := by rwa [sup_comm]
  rw [← SetLike.mem_coe, Subgroup.mul_normal X (layer A)] at hn'
  obtain ⟨x, hx, k, hk, rfl⟩ := hn'
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hz2 : zb ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hd.z2
  have hkinn : layerHom A k⁻¹ ∈ innSub ↥(layer A) := by
    rw [← map_layer_layerHom]; exact Subgroup.mem_map_of_mem _ ((layer A).inv_mem hk)
  have hxX : layerHom A x ∈ X.map (layerHom A) := Subgroup.mem_map_of_mem _ hx
  rcases Int.even_or_odd' m with ⟨j, rfl | rfl⟩
  · beta_reduce at ha ⊢
    rw [zpow_mul, hz2, one_zpow, one_mul] at ha ⊢
    rw [map_mul] at ha
    have h1 : layerHom A x = layerHom A k⁻¹ := by
      rw [map_inv]; exact eq_inv_of_mul_eq_one_left ha
    have h2 : layerHom A x ∈ X.map (layerHom A) ⊓ innSub ↥(layer A) := ⟨hxX, h1 ▸ hkinn⟩
    rw [hXI, Subgroup.mem_bot] at h2
    have hx1 : x = 1 := hXker x hx h2
    rw [hx1, map_one, one_mul] at ha
    have hk1 : k = 1 := hKker k hk ha
    rw [hx1, hk1]; simp
  · exfalso
    beta_reduce at ha
    rw [zpow_add_one, zpow_mul, hz2, one_zpow, one_mul] at ha
    rw [map_mul, map_mul] at ha
    apply hα
    rw [← layerHom_eq_layerAut]
    have h3 : layerHom A zb = (layerHom A x * layerHom A k)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left ha
    have hkinn' : (layerHom A k)⁻¹ ∈ innSub ↥(layer A) := by rw [← map_inv]; exact hkinn
    rw [h3, mul_inv_rev]
    exact (innSub ↥(layer A) ⊔ X.map (layerHom A)).mul_mem
      (Subgroup.mem_sup_left hkinn') (Subgroup.mem_sup_right ((X.map (layerHom A)).inv_mem hxX))

theorem ftwo_L34_transport {zb : A} {p : ℕ} {X : Subgroup A} (hd : CellData zb p X)
    (hZ : center ↥(layer A) = ⊥) (hL : LieModel ↥(layer A) .PSL 3 2 2) (hAut : L34Aut) :
    IsPGL3Four ↥(layer A ⊔ X) ∧ Nat.card ↥X = 3 ∧
      layer A ⊓ centralizer ({zb} : Set A) = layer A ⊓ centralizer (X : Set A) ∧
      IVK.IsL2 ↥(layer A ⊓ centralizer ({zb} : Set A)) (fun q => q = 4) ∧
      (layer A ⊔ X ⊔ zpowers zb) ⊓ centralizer ((layer A ⊓ centralizer ({zb} : Set A) : Subgroup A) : Set A) =
        X ⊔ zpowers zb := by
  classical
  obtain ⟨hc3, hXI, hα, hPGL, hcent, hL2, hCJ⟩ :=
    hAut ↥(layer A) hL (layerAut zb) p (X.map (layerHom A)) (autCfg_of_cellData hd hZ)
  have hinj := layerHom_injective_of_aut hd hZ hXI hα
  have hK : (layer A).map (layerHom A) = innSub ↥(layer A) := map_layer_layerHom
  have hα' : layerAut zb = layerHom A zb := (layerHom_eq_layerAut zb).symm
  rw [hα'] at hα hcent hL2 hCJ
  have hmemK : ∀ k ∈ layer A, layerHom A k ∈ innSub ↥(layer A) := fun k hk => by
    rw [← hK]; exact Subgroup.mem_map_of_mem _ hk
  have hinK : ∀ c ∈ innSub ↥(layer A), ∃ k ∈ layer A, layerHom A k = c := fun c hc => by
    rw [← hK] at hc; obtain ⟨k, hk, rfl⟩ := hc; exact ⟨k, hk, rfl⟩
  have hcom : ∀ a b : A, a * b = b * a ↔ layerHom A a * layerHom A b = layerHom A b * layerHom A a :=
    fun a b => by rw [← map_mul, ← map_mul]; exact hinj.eq_iff.symm
  have hmemsup : ∀ (U V : Subgroup A) (a : A),
      a ∈ U ⊔ V ↔ layerHom A a ∈ U.map (layerHom A) ⊔ V.map (layerHom A) := by
    intro U V a
    rw [← Subgroup.map_sup]
    exact (Subgroup.mem_map_iff_mem hinj).symm
  have hJ : (layer A ⊓ centralizer ({zb} : Set A)).map (layerHom A) =
      innSub ↥(layer A) ⊓ centralizer ({layerHom A zb} : Set (MulAut ↥(layer A))) := by
    ext c
    constructor
    · rintro ⟨k, ⟨hk, hkz⟩, rfl⟩
      exact ⟨hmemK k hk, Subgroup.mem_centralizer_singleton_iff.mpr
        ((hcom _ _).mp (Subgroup.mem_centralizer_singleton_iff.mp hkz))⟩
    · rintro ⟨hc, hcz⟩
      obtain ⟨k, hk, rfl⟩ := hinK c hc
      exact ⟨k, ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr
        ((hcom _ _).mpr (Subgroup.mem_centralizer_singleton_iff.mp hcz))⟩, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    have e1 := Subgroup.equivMapOfInjective (layer A ⊔ X) (layerHom A) hinj
    have h1 : (layer A ⊔ X).map (layerHom A) = innSub ↥(layer A) ⊔ X.map (layerHom A) := by
      rw [Subgroup.map_sup, hK]
    exact Transport.isPGL3Four_of_mulEquiv (e1.trans (MulEquiv.subgroupCongr h1)).symm hPGL
  · rw [← Subgroup.card_map_of_injective hinj]; exact hc3
  ·
    ext k
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hk, hkz⟩
      refine ⟨hk, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      have h1 : layerHom A k ∈ innSub ↥(layer A) ⊓
          centralizer ({layerHom A zb} : Set (MulAut ↥(layer A))) :=
        ⟨hmemK k hk, Subgroup.mem_centralizer_singleton_iff.mpr
          ((hcom _ _).mp (Subgroup.mem_centralizer_singleton_iff.mp hkz))⟩
      rw [hcent] at h1
      have h2 := Subgroup.mem_centralizer_iff.mp h1.2 (layerHom A x) (Subgroup.mem_map_of_mem _ hx)
      exact (hcom x k).mpr h2
    · rintro ⟨hk, hkx⟩
      refine ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : layerHom A k ∈ innSub ↥(layer A) ⊓
          centralizer ((X.map (layerHom A) : Subgroup _) : Set (MulAut ↥(layer A))) :=
        ⟨hmemK k hk, Subgroup.mem_centralizer_iff.mpr (by
          rintro _ ⟨x, hx, rfl⟩
          exact (hcom x k).mp (Subgroup.mem_centralizer_iff.mp hkx x hx))⟩
      rw [← hcent] at h1
      exact (hcom k zb).mpr (Subgroup.mem_centralizer_singleton_iff.mp h1.2)
  ·
    have e1 := Subgroup.equivMapOfInjective (layer A ⊓ centralizer ({zb} : Set A)) (layerHom A) hinj
    exact Transport.isL2_of_mulEquiv (e1.trans (MulEquiv.subgroupCongr hJ)).symm hL2
  ·
    ext a
    rw [Subgroup.mem_inf]
    constructor
    · rintro ⟨ha, hac⟩
      have h1 : layerHom A a ∈ (innSub ↥(layer A) ⊔ X.map (layerHom A) ⊔ zpowers (layerHom A zb)) ⊓
          centralizer ((innSub ↥(layer A) ⊓
            centralizer ({layerHom A zb} : Set (MulAut ↥(layer A))) : Subgroup _) :
            Set (MulAut ↥(layer A))) := by
        refine ⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
        · have := (hmemsup (layer A ⊔ X) (zpowers zb) a).mp ha
          rw [Subgroup.map_sup, hK, MonoidHom.map_zpowers] at this
          exact this
        · intro c hc
          rw [← hJ] at hc
          obtain ⟨k, hkJ, rfl⟩ := hc
          exact (hcom k a).mp (Subgroup.mem_centralizer_iff.mp hac k hkJ)
      rw [hCJ] at h1
      exact (hmemsup X (zpowers zb) a).mpr (by rw [MonoidHom.map_zpowers]; exact h1)
    · intro ha
      have h1 := (hmemsup X (zpowers zb) a).mp ha
      rw [MonoidHom.map_zpowers] at h1
      rw [← hCJ] at h1
      have hle : X ⊔ zpowers zb ≤ layer A ⊔ X ⊔ zpowers zb :=
        sup_le (le_sup_right.trans le_sup_left) le_sup_right
      refine ⟨hle ha, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro k hk
      have hρk : layerHom A k ∈ innSub ↥(layer A) ⊓
          centralizer ({layerHom A zb} : Set (MulAut ↥(layer A))) := by
        rw [← hJ]; exact Subgroup.mem_map_of_mem _ hk
      exact (hcom k a).mpr (Subgroup.mem_centralizer_iff.mp h1.2 _ hρk)

end Inj

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
