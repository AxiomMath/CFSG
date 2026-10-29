module

public import CFSG.LocalAnalysis.GL83PartI.I_20_1
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec11Small

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

namespace Lemma1114

variable {G : Type} [Group G] [Finite G]

theorem top_layer_eq_bot {p : ℕ} (hp : p.Prime) (C : Subgroup G)
    (h : GLAPLayer p C = ⊥) : GLAPLayer p (⊤ : Subgroup C) = ⊥ := by
  have hle : GLAPLayer p (⊤ : Subgroup C) ≤ (GLAPLayer p C).comap C.subtype := by
    unfold GLAPLayer
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hker : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup C) ⊓ C.subtype.ker)) := by
      have : (⊤ : Subgroup C) ⊓ C.subtype.ker = ⊥ := by simp
      rw [this, Subgroup.card_bot]
      exact Nat.coprime_one_right p
    have h1 := glaPComponent_map hp C.subtype hker hJ
    have htop : (⊤ : Subgroup C).map C.subtype = C :=
      le_antisymm (by rintro _ ⟨y, -, rfl⟩; exact y.2) fun y hy => ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
    rw [htop] at h1
    exact le_sSup h1
  rw [h, MonoidHom.comap_bot, Subgroup.ker_subtype] at hle
  exact le_bot_iff.1 hle

theorem top_primeCoreOf_eq (p : ℕ) (X : Type) [Group X] :
    GLAPPrimeCoreOf p (⊤ : Subgroup X) = GLAPPrimeCore p X := by
  have h := glaPPrimeCore_map_iso p (Subgroup.topEquiv (G := X))
  have hsub : (⊤ : Subgroup X).subtype = (Subgroup.topEquiv (G := X)).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  unfold GLAPPrimeCoreOf
  rw [hsub, h]

theorem bender_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {C B : Subgroup G}
    (hlayer : GLAPLayer p C = ⊥) (hB : IsElemAbelian p B) (hBC : B ≤ C)
    (hmax : ∀ F : Subgroup G, F ≤ C → IsElemAbelian p F → B ≤ F → F = B)
    {Y : Subgroup G} (hY : Y ≤ C) (hcop : Nat.Coprime p (Nat.card Y))
    (hBY : B ≤ Subgroup.normalizer (Y : Set G)) :
    Y ≤ GLAPPrimeCoreOf p C := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hBmap : (B.subgroupOf C).map C.subtype = B := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hBC]
  have hB'el : IsElemAbelian p (B.subgroupOf C) := CFSG.Open.IsElemAbelian.subgroupOf hB C
  have hmax' : ∀ F : Subgroup ↥C, IsElemAbelian p F → B.subgroupOf C ≤ F →
      F = B.subgroupOf C := by
    intro F hF hBF
    have hF0 := hmax (F.map C.subtype) (Subgroup.map_subtype_le F)
      (CFSG.Open.IsElemAbelian.map hF C.subtype) (by rw [← hBmap]; exact Subgroup.map_mono hBF)
    apply Subgroup.map_injective (f := C.subtype) (fun a b h => Subtype.ext h)
    rw [hF0, hBmap]
  have hY' : Nat.Coprime p (Nat.card (Y.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv]
    exact hcop
  have hBY' : B.subgroupOf C ≤ Subgroup.normalizer ((Y.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hx' := Subgroup.mem_normalizer_iff.1 (hBY (Subgroup.mem_subgroupOf.1 hx)) (h : G)
    simpa [Subgroup.mem_subgroupOf] using hx'
  have key := GL83.I_20_1_proved C p hp hp2 (top_layer_eq_bot hp C hlayer) (B.subgroupOf C)
    hB'el hmax'
  have hle : Y.subgroupOf C ≤ GLAPPrimeCoreOf p (⊤ : Subgroup C) := by
    rw [← key]
    exact le_iSup_of_le (Y.subgroupOf C) (le_iSup_of_le hY' (le_iSup_of_le hBY' le_rfl))
  rw [top_primeCoreOf_eq] at hle
  intro y hy
  exact ⟨⟨y, hY hy⟩, hle (show (⟨y, hY hy⟩ : C) ∈ Y.subgroupOf C from Subgroup.mem_subgroupOf.2 hy), rfl⟩


set_option warn.classDefReducibility false in
@[expose] noncomputable def conjAct (A T : Subgroup G) (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    MulDistribMulAction ↥A ↥T where
  smul a t := ⟨(a : G) * t * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.1 (hAT a.2) t).1 t.2⟩
  one_smul t := Subtype.ext (show ((1 : ↥A) : G) * (t : G) * ((1 : ↥A) : G)⁻¹ = (t : G) by simp)
  mul_smul a b t := Subtype.ext (show ((a * b : ↥A) : G) * (t : G) * ((a * b : ↥A) : G)⁻¹ =
    (a : G) * ((b : G) * (t : G) * (b : G)⁻¹) * (a : G)⁻¹ by simp [mul_assoc])
  smul_mul a t s := Subtype.ext (show (a : G) * ((t : G) * (s : G)) * (a : G)⁻¹ =
    ((a : G) * (t : G) * (a : G)⁻¹) * ((a : G) * (s : G) * (a : G)⁻¹) by simp [mul_assoc])
  smul_one a := Subtype.ext (show (a : G) * 1 * (a : G)⁻¹ = 1 by simp)

theorem gen_by_hyperplanes {p : ℕ} (hp : p.Prime) {A T : Subgroup G} (hAel : IsElemAbelian p A)
    (hA1 : A ≠ ⊥) (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hT : ¬ p ∣ Nat.card T) :
    T ≤ ⨆ (D : Subgroup G) (_ : D ≤ A ∧ (D.subgroupOf A).index = p),
      T ⊓ Subgroup.centralizer (D : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CFSG.IsElementaryAbelian p ↥A := hAel.isElementaryAbelian
  haveI : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).2 hA1
  letI := conjAct A T hAT
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := ↥A) (H := ↥T) hT
  have hle : (⨆ (B : Subgroup ↥A) (_ : B.index = p), fixedPointSubgroup B ↥T).map T.subtype ≤
      ⨆ (D : Subgroup G) (_ : D ≤ A ∧ (D.subgroupOf A).index = p),
        T ⊓ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun B => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hB => ?_
    rintro _ ⟨z, hz, rfl⟩
    have hBD : (B.map A.subtype).subgroupOf A = B := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    have hcond : B.map A.subtype ≤ A ∧ ((B.map A.subtype).subgroupOf A).index = p :=
      ⟨Subgroup.map_subtype_le B, by rw [hBD]; exact hB⟩
    refine Subgroup.mem_iSup_of_mem (B.map A.subtype) (Subgroup.mem_iSup_of_mem hcond ?_)
    refine Subgroup.mem_inf.2 ⟨z.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hfix := (FixedPoints.mem_subgroup (M := ↥B) (α := ↥T) z).1 hz ⟨b, hb⟩
    have hval := congrArg Subtype.val hfix
    change (b : G) * (z : G) * (b : G)⁻¹ = (z : G) at hval
    show (b : G) * (z : G) = (z : G) * (b : G)
    calc (b : G) * (z : G) = ((b : G) * (z : G) * (b : G)⁻¹) * (b : G) := by group
      _ = (z : G) * (b : G) := by rw [hval]
  have htop := hle
  rw [hgen] at htop
  intro x hx
  exact htop (Subgroup.mem_map.2 ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩)


def prodHom (H K : Subgroup G) (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) : ↥H × ↥K →* G :=
  { toFun := fun p => (p.1 : G) * (p.2 : G)
    map_one' := by simp
    map_mul' := fun p q => by
      have hcomm := hc (q.1 : G) q.1.2 (p.2 : G) p.2.2
      simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
      calc (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G))
          = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
        _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by rw [hcomm]
        _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by group }

theorem range_prodHom (H K : Subgroup G) (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    (prodHom H K hc).range = H ⊔ K := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨⟨h, k⟩, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h.2) (Subgroup.mem_sup_right k.2)
  · refine sup_le ?_ ?_
    · intro h hh
      exact ⟨(⟨h, hh⟩, 1), by simp [prodHom]⟩
    · intro k hk
      exact ⟨(1, ⟨k, hk⟩), by simp [prodHom]⟩

theorem mem_sup_prod {H K : Subgroup G} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G}
    (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  rw [← range_prodHom H K hc] at hx
  obtain ⟨⟨h, k⟩, hp⟩ := hx
  exact ⟨h, h.2, k, k.2, hp.symm⟩

theorem card_sup_mul_card_inf (H K : Subgroup G) (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  have hker : Nat.card (prodHom H K hc).ker = Nat.card ↥(H ⊓ K) := by
    have hK : ∀ p : (prodHom H K hc).ker, (p.1.1 : G) ∈ K := by
      intro p
      have hp : (p.1.1 : G) * (p.1.2 : G) = 1 := p.2
      have : (p.1.1 : G) = (p.1.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left hp
      rw [this]
      exact K.inv_mem p.1.2.2
    refine Nat.card_congr
      { toFun := fun p => ⟨(p.1.1 : G), Subgroup.mem_inf.2 ⟨p.1.1.2, hK p⟩⟩
        invFun := fun z => ⟨(⟨(z : G), (Subgroup.mem_inf.1 z.2).1⟩,
          ⟨(z : G)⁻¹, K.inv_mem (Subgroup.mem_inf.1 z.2).2⟩), MonoidHom.mem_ker.2 (by simp [prodHom])⟩
        left_inv := fun p => ?_
        right_inv := fun z => Subtype.ext rfl }
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      have hp : (p.1.1 : G) * (p.1.2 : G) = 1 := p.2
      show ((p.1.1 : G))⁻¹ = (p.1.2 : G)
      exact inv_eq_of_mul_eq_one_right hp
  have h1 := Subgroup.card_mul_index (prodHom H K hc).ker
  rw [Subgroup.index_ker, range_prodHom, hker, Nat.card_prod] at h1
  rw [← h1]
  ring

theorem card_le_of_elemAb_le {H F : Subgroup G} (hF : IsElemAbelian 3 F) (hFH : F ≤ H) :
    Nat.card F ≤ 3 ^ CFSG.Open.pRank 3 H := by
  obtain ⟨r, hr⟩ := exists_card_eq_pow (CFSG.Open.IsElemAbelian.isPGroup hF)
  rw [hr]
  exact Nat.pow_le_pow_right (by norm_num) (CFSG.SectionRank.le_pRank (by norm_num) hFH hF hr)

theorem card_eq_pow_of_pRank {A : Subgroup G} (hA : IsElemAbelian 3 A) :
    Nat.card A = 3 ^ CFSG.Open.pRank 3 A := by
  have hle := card_le_of_elemAb_le (H := A) hA le_rfl
  obtain ⟨E₀, hE₀le, _, hE₀card⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) A
  have hge : Nat.card E₀ ≤ Nat.card A := Subgroup.card_le_of_le hE₀le
  rw [hE₀card] at hge
  omega

theorem card_eq_27_of_pRank {A : Subgroup G} (hA : IsElemAbelian 3 A)
    (hr : CFSG.Open.pRank 3 A = 3) : Nat.card A = 27 := by
  rw [card_eq_pow_of_pRank hA, hr]
  norm_num

theorem card_of_index_three {A D : Subgroup G} (hDA : D ≤ A) (hA27 : Nat.card A = 27)
    (hD : (D.subgroupOf A).index = 3) : Nat.card D = 9 := by
  have h1 := Subgroup.card_mul_index (D.subgroupOf A)
  rw [hD, hA27, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv] at h1
  omega

theorem le_normalizer_inf_centralizer {A T : Subgroup G} {e : G}
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hAc : ∀ x ∈ A, x * e = e * x) :
    A ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) : Set G) := by
  have key : ∀ x ∈ A, ∀ y ∈ T ⊓ Subgroup.centralizer ({e} : Set G),
      x * y * x⁻¹ ∈ T ⊓ Subgroup.centralizer ({e} : Set G) := by
    intro x hx y hy
    rw [Subgroup.mem_inf] at hy ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hAT hx) y).1 hy.1, ?_⟩
    have hy' : e * y = y * e := Subgroup.mem_centralizer_iff.1 hy.2 e (Set.mem_singleton e)
    have h1 : x * e = e * x := hAc x hx
    have hxinv : x⁻¹ * e = e * x⁻¹ := by
      calc x⁻¹ * e = x⁻¹ * (e * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * e) * x⁻¹ := by rw [h1]
        _ = e * x⁻¹ := by group
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    calc h * (x * y * x⁻¹) = (h * x) * y * x⁻¹ := by group
      _ = (x * h) * y * x⁻¹ := by rw [← h1]
      _ = x * (h * y) * x⁻¹ := by group
      _ = x * (y * h) * x⁻¹ := by rw [hy']
      _ = x * y * (h * x⁻¹) := by group
      _ = x * y * (x⁻¹ * h) := by rw [hxinv]
      _ = x * y * x⁻¹ * h := by group
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key x hx y
  · intro hy
    have h2 := key x⁻¹ (A.inv_mem hx) _ hy
    convert h2 using 1
    group

theorem elemAb_comm {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (isMulCommutative_iff.1 hE.1 ⟨x, hx⟩ ⟨y, hy⟩)

theorem card_of_index_three_gen {A D : Subgroup G} (hDA : D ≤ A) {n : ℕ} (hA : Nat.card A = n)
    (hD : (D.subgroupOf A).index = 3) : Nat.card D * 3 = n := by
  have h1 := Subgroup.card_mul_index (D.subgroupOf A)
  rw [hD, hA, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv] at h1
  exact h1

theorem partA {M E A T : Subgroup G} (hAM : A ≤ M) (hAel : IsElemAbelian 3 A)
    (hAmax : ∀ F : Subgroup G, F ≤ M → IsElemAbelian 3 F → A ≤ F → F = A)
    (hA0 : CFSG.Open.pRank 3 (E ⊓ A) = 2)
    (h13 : ∀ e ∈ E ⊓ A, e ≠ 1 →
      GLAPLayer 3 (M ⊓ Subgroup.centralizer ({e} : Set G)) = ⊥ ∧
        GLAPPrimeCoreOf 3 (M ⊓ Subgroup.centralizer ({e} : Set G)) ≤ GLAPPrimeCoreOf 3 M)
    (hTM : T ≤ M) (hT : ¬ 3 ∣ Nat.card T) (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ GLAPPrimeCoreOf 3 M := by
  have hA0el : IsElemAbelian 3 (E ⊓ A : Subgroup G) := CFSG.Open.IsElemAbelian.mono hAel inf_le_right
  have hA0card : Nat.card ((E ⊓ A : Subgroup G)) = 9 := by
    rw [card_eq_pow_of_pRank hA0el, hA0]
    norm_num
  have hA0ne : E ⊓ A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA0card
    norm_num at hA0card
  have hA0T : E ⊓ A ≤ Subgroup.normalizer (T : Set G) := fun x hx => hAT (Subgroup.mem_inf.1 hx).2
  have hgen := gen_by_hyperplanes (p := 3) Nat.prime_three hA0el hA0ne hA0T hT
  refine hgen.trans (iSup₂_le fun D hD => ?_)
  obtain ⟨hDA0, hD3⟩ := hD
  have hDcard := card_of_index_three_gen hDA0 hA0card hD3
  have hD1 : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDcard
    omega
  obtain ⟨e, he, he1⟩ : ∃ e ∈ D, e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hD1
    exact (Subgroup.eq_bot_iff_forall D).2 fun x hx => by simpa using hcon x hx
  have he_A0 : e ∈ E ⊓ A := hDA0 he
  have he_A : e ∈ A := (Subgroup.mem_inf.1 he_A0).2
  have hsub : T ⊓ Subgroup.centralizer (D : Set G) ≤ T ⊓ Subgroup.centralizer ({e} : Set G) :=
    inf_le_inf_left T (Subgroup.centralizer_le (Set.singleton_subset_iff.2 he))
  refine hsub.trans ?_
  have hC := h13 e he_A0 he1
  have hBC : A ≤ M ⊓ Subgroup.centralizer ({e} : Set G) := by
    refine le_inf hAM fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact elemAb_comm hAel he_A hx
  have hcop : Nat.Coprime 3 (Nat.card ((T ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G))) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => hT ?_
    exact h.trans (Subgroup.card_dvd_of_le (inf_le_left : (T ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) ≤ T))
  have hbend := bender_prime (p := 3) Nat.prime_three (by norm_num) hC.1 hAel hBC
    (fun F hFC hF hAF => hAmax F (hFC.trans inf_le_left) hF hAF)
    (Y := T ⊓ Subgroup.centralizer ({e} : Set G))
    (inf_le_inf_right _ hTM |>.trans (le_refl _)) hcop
    (le_normalizer_inf_centralizer hAT fun x hx => elemAb_comm hAel hx he_A)
  exact hbend.trans hC.2

theorem le_normalizer_inf_centralizer_set {A T : Subgroup G} {S : Set G}
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hAc : ∀ x ∈ A, ∀ s ∈ S, x * s = s * x) :
    A ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer S : Subgroup G) : Set G) := by
  have key : ∀ x ∈ A, ∀ y ∈ T ⊓ Subgroup.centralizer S, x * y * x⁻¹ ∈ T ⊓ Subgroup.centralizer S := by
    intro x hx y hy
    rw [Subgroup.mem_inf] at hy ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hAT hx) y).1 hy.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hy' : h * y = y * h := Subgroup.mem_centralizer_iff.1 hy.2 h hh
    have h1 : x * h = h * x := hAc x hx h hh
    have hxinv : x⁻¹ * h = h * x⁻¹ := by
      calc x⁻¹ * h = x⁻¹ * (h * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * h) * x⁻¹ := by rw [h1]
        _ = h * x⁻¹ := by group
    calc h * (x * y * x⁻¹) = (h * x) * y * x⁻¹ := by group
      _ = (x * h) * y * x⁻¹ := by rw [← h1]
      _ = x * (h * y) * x⁻¹ := by group
      _ = x * (y * h) * x⁻¹ := by rw [hy']
      _ = x * y * (h * x⁻¹) := by group
      _ = x * y * (x⁻¹ * h) := by rw [hxinv]
      _ = x * y * x⁻¹ * h := by group
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key x hx y
  · intro hy
    have h2 := key x⁻¹ (A.inv_mem hx) _ hy
    convert h2 using 1
    group

theorem mem_centralizer_of_comm {A : Subgroup G} (hA : IsElemAbelian 3 A) {S : Set G} (hS : S ⊆ A)
    {x : G} (hx : x ∈ A) : x ∈ Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact elemAb_comm hA (hS hh) hx

theorem exists_inter_nontrivial {A A₀ D : Subgroup G} (hA : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hA₀A : A₀ ≤ A) (hA₀card : Nat.card A₀ = 9)
    (hDA : D ≤ A) (hDcard : Nat.card D = 9) (hD : D ≠ A₀) :
    ∃ e ∈ D ⊓ A₀, e ≠ 1 := by
  have hcomm : ∀ h ∈ D, ∀ k ∈ A₀, h * k = k * h := fun h hh k hk =>
    elemAb_comm hA (hDA hh) (hA₀A hk)
  have hprod := card_sup_mul_card_inf D A₀ hcomm
  have hsup : Nat.card ↥(D ⊔ A₀) ≤ 27 := by
    rw [← hA27]
    exact Subgroup.card_le_of_le (sup_le hDA hA₀A)
  rw [hDcard, hA₀card] at hprod
  have hinter : 3 ≤ Nat.card ↥(D ⊓ A₀) := by
    by_contra hlt
    have hle2 : Nat.card ↥(D ⊓ A₀) ≤ 2 := by omega
    have hmul := Nat.mul_le_mul hsup hle2
    rw [hprod] at hmul
    norm_num at hmul
  have hne : D ⊓ A₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hinter
    omega
  obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  exact ⟨e, he, fun h => he1 (Subtype.ext h)⟩

@[expose] def Lemma1114FusionInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (_h : Cex117 G m p B M E A a K), p = 3 → IsLThreeFour (barOf 3 K) →
    ∀ x ∈ E ⊓ A, x ≠ 1 → ∀ y ∈ E ⊓ A, y ≠ 1 →
      ∃ n ∈ K, n ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ∧ n⁻¹ * x * n = y

@[expose] def Lemma1114ChiefInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (_h : Cex117 G m p B M E A a K), p = 3 → IsLThreeFour (barOf 3 K) →
    ∀ a₁ ∈ A, a₁ ∉ E ⊓ A → ∀ K₁ : Subgroup G, GLAPComponent 3 (Cg a₁) K₁ →
      IsLThreeFour (barOf 3 K₁) →
      ∀ S : Subgroup G, S ≤ Cg a₁ → ¬ 3 ∣ Nat.card S → A ≤ Subgroup.normalizer (S : Set G) →
        S ≤ K₁ ⊔ GLAPPrimeCoreOf 3 (Cg a₁) ⊔ Subgroup.centralizer (A : Set G)

@[expose] def Lemma1114ConstrInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (_h : Cex117 G m p B M E A a K), p = 3 → IsLThreeFour (barOf 3 K) →
    ∀ e ∈ E ⊓ A, e ≠ 1 → GLAPLayer 3 (Subgroup.centralizer ({e, a} : Set G)) = ⊥

theorem partB_aD {M E A T D : Subgroup G} {a : G} (hAM : A ≤ M) (hAel : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27)
    (hAmax : ∀ F : Subgroup G, F ≤ M → IsElemAbelian 3 F → A ≤ F → F = A)
    (hA0el : IsElemAbelian 3 (E ⊓ A : Subgroup G)) (hA0card : Nat.card ((E ⊓ A : Subgroup G)) = 9)
    (hCa : CFSG.Open.pRank 3 (Subgroup.centralizer ({a} : Set G)) = 3)
    (ha : a ∈ A)
    (hF3 : ∀ e ∈ E ⊓ A, e ≠ 1 → GLAPLayer 3 (Subgroup.centralizer ({e, a} : Set G)) = ⊥)
    (h112 : ∀ e ∈ E ⊓ A, e ≠ 1 → GLAPPrimeCoreOf 3 (Subgroup.centralizer ({e, a} : Set G)) ≤ M ∨
      ∃ A₁ : Subgroup G, inD 3 M A₁ ∧ a ∈ A₁)
    (hnotD : ¬ ∃ A₁ : Subgroup G, inD 3 M A₁ ∧ a ∈ A₁)
    (hT : ¬ 3 ∣ Nat.card T) (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hDA : D ≤ A) (hDcard : Nat.card D = 9) (hD : D ≠ E ⊓ A) (haD : a ∈ D) :
    T ⊓ Subgroup.centralizer (D : Set G) ≤ M := by
  obtain ⟨e, he, he1⟩ := exists_inter_nontrivial hAel hA27 (inf_le_right : E ⊓ A ≤ A) hA0card hDA
    hDcard hD
  have heA0 : e ∈ E ⊓ A := (Subgroup.mem_inf.1 he).2
  have heD : e ∈ D := (Subgroup.mem_inf.1 he).1
  have hYC : T ⊓ Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer ({e, a} : Set G) := by
    intro x hx
    have hxC : ∀ h ∈ D, h * x = x * h := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl
    · exact hxC _ heD
    · exact hxC _ haD
  have hBC : A ≤ Subgroup.centralizer ({e, a} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl
    · exact elemAb_comm hAel (Subgroup.mem_inf.1 heA0).2 hx
    · exact elemAb_comm hAel ha hx
  have hmax : ∀ F : Subgroup G, F ≤ Subgroup.centralizer ({e, a} : Set G) → IsElemAbelian 3 F →
      A ≤ F → F = A := by
    intro F hFC hF hAF
    have hFa : F ≤ Subgroup.centralizer ({a} : Set G) := by
      refine hFC.trans (Subgroup.centralizer_le ?_)
      intro x hx
      exact Set.mem_insert_of_mem _ hx
    have hcardF := card_le_of_elemAb_le (H := Subgroup.centralizer ({a} : Set G)) hF hFa
    rw [hCa] at hcardF
    have hcardA : Nat.card A ≤ Nat.card F := Subgroup.card_le_of_le hAF
    exact (Subgroup.eq_of_le_of_card_ge hAF (by omega)).symm
  have hcop : ¬ 3 ∣ Nat.card ((T ⊓ Subgroup.centralizer (D : Set G) : Subgroup G)) := fun h =>
    hT (h.trans (Subgroup.card_dvd_of_le
      (inf_le_left : (T ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) ≤ T)))
  have hbend := bender_prime (p := 3) Nat.prime_three (by norm_num) (hF3 e heA0 he1) hAel hBC hmax
    hYC (Y := T ⊓ Subgroup.centralizer (D : Set G))
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hcop)
    (le_normalizer_inf_centralizer_set hAT fun x hx s hs => elemAb_comm hAel hx (hDA hs))
  rcases h112 e heA0 he1 with h | ⟨A₁, hA₁, haA₁⟩
  · exact hbend.trans h
  · exact absurd ⟨A₁, hA₁, haA₁⟩ hnotD

theorem coord_setup {A A₀ : Subgroup G} {a : G} (hAel : IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hA₀A : A₀ ≤ A) (hA₀card : Nat.card ↥A₀ = 9) (ha : a ∈ A) (ha1 : a ≠ 1)
    (haA₀ : a ∉ A₀) :
    A₀ ⊓ Subgroup.zpowers a = ⊥ ∧ A₀ ⊔ Subgroup.zpowers a = A := by
  have ha3 : a ^ 3 = 1 := hAel.2 a ha
  have hcomm : ∀ h ∈ A₀, ∀ k ∈ Subgroup.zpowers a, h * k = k * h := by
    intro h hh k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hc : Commute h a := elemAb_comm hAel (hA₀A hh) ha
    exact hc.zpow_right n
  have hz : Nat.card ↥(Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have hinter : Nat.card ↥(A₀ ⊓ Subgroup.zpowers a) = 1 := by
    have hdvd : Nat.card ↥(A₀ ⊓ Subgroup.zpowers a) ∣ 3 := by
      rw [← hz]
      exact Subgroup.card_dvd_of_le (inf_le_right : A₀ ⊓ Subgroup.zpowers a ≤ Subgroup.zpowers a)
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact h
    · exfalso
      apply haA₀
      have heq : A₀ ⊓ Subgroup.zpowers a = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
      have hmem : a ∈ A₀ ⊓ Subgroup.zpowers a := by
        rw [heq]
        exact Subgroup.mem_zpowers a
      exact (Subgroup.mem_inf.1 hmem).1
  have hbot : A₀ ⊓ Subgroup.zpowers a = ⊥ := Subgroup.eq_bot_of_card_eq _ hinter
  refine ⟨hbot, ?_⟩
  have hprod := card_sup_mul_card_inf A₀ (Subgroup.zpowers a) hcomm
  rw [hA₀card, hz, hinter] at hprod
  have hsupA : A₀ ⊔ Subgroup.zpowers a ≤ A :=
    sup_le hA₀A ((Subgroup.zpowers_le).2 ha)
  exact Subgroup.eq_of_le_of_card_ge hsupA (by omega)

theorem coord_decomp {A A₀ : Subgroup G} {a : G} (hAel : IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hA₀A : A₀ ≤ A) (hA₀card : Nat.card ↥A₀ = 9) (ha : a ∈ A) (ha1 : a ≠ 1)
    (haA₀ : a ∉ A₀) {x : G} (hx : x ∈ A) :
    ∃ x₀ ∈ A₀, ∃ i : ℕ, i < 3 ∧ x = x₀ * a ^ i := by
  obtain ⟨_, hsup⟩ := coord_setup hAel hA27 hA₀A hA₀card ha ha1 haA₀
  have ha3 : a ^ 3 = 1 := hAel.2 a ha
  have hcomm : ∀ h ∈ A₀, ∀ k ∈ Subgroup.zpowers a, h * k = k * h := by
    intro h hh k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hc : Commute h a := elemAb_comm hAel (hA₀A hh) ha
    exact hc.zpow_right n
  have hx' : x ∈ A₀ ⊔ Subgroup.zpowers a := hsup ▸ hx
  obtain ⟨x₀, hx₀, k, hk, rfl⟩ := mem_sup_prod hcomm hx'
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hmod : a ^ (n % (3 : ℕ)) = a ^ n := by
    have := zpow_mod_orderOf a n
    rwa [orderOf_eq_prime ha3 ha1] at this
  refine ⟨x₀, hx₀, (n % (3 : ℤ)).toNat, ?_, ?_⟩
  · have h0 : 0 ≤ n % (3 : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h1 : n % (3 : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
    omega
  · have h0 : 0 ≤ n % (3 : ℤ) := Int.emod_nonneg _ (by norm_num)
    rw [← zpow_natCast, Int.toNat_of_nonneg h0]
    have : a ^ (n % (3 : ℤ)) = a ^ n := by
      have := zpow_mod_orderOf a n
      rwa [orderOf_eq_prime ha3 ha1] at this
    rw [this]

theorem mem_map_conj {T : Subgroup G} {y z : G} :
    z ∈ T.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * z * y ∈ T := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply, mul_assoc]

theorem partB_alpha {M E A T D : Subgroup G} {a y : G} (hAM : A ≤ M) (hAel : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27)
    (hAmax : ∀ F : Subgroup G, F ≤ M → IsElemAbelian 3 F → A ≤ F → F = A)
    (hA0el : IsElemAbelian 3 (E ⊓ A : Subgroup G)) (hA0card : Nat.card ((E ⊓ A : Subgroup G)) = 9)
    (hCa : CFSG.Open.pRank 3 (Subgroup.centralizer ({a} : Set G)) = 3)
    (ha : a ∈ A) (haA0 : a ∉ E ⊓ A)
    (hF3 : ∀ e ∈ E ⊓ A, e ≠ 1 → GLAPLayer 3 (Subgroup.centralizer ({e, a} : Set G)) = ⊥)
    (h112 : ∀ e ∈ E ⊓ A, e ≠ 1 → GLAPPrimeCoreOf 3 (Subgroup.centralizer ({e, a} : Set G)) ≤ M ∨
      ∃ A₁ : Subgroup G, inD 3 M A₁ ∧ a ∈ A₁)
    (hnotD : ¬ ∃ A₁ : Subgroup G, inD 3 M A₁ ∧ a ∈ A₁)
    (hyM : y ∈ M) (hyA : y ∈ Subgroup.normalizer (A : Set G)) (hay : y⁻¹ * a * y ∈ D)
    (hT : ¬ 3 ∣ Nat.card T) (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hDA : D ≤ A) (hDcard : Nat.card D = 9) :
    T ⊓ Subgroup.centralizer (D : Set G) ≤ M := by
  have hyA' : ∀ z : G, z ∈ A ↔ y * z * y⁻¹ ∈ A := fun z => Subgroup.mem_normalizer_iff.1 hyA z
  have hT₁card : Nat.card (T.map (MulAut.conj y).toMonoidHom) = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hD₁card : Nat.card (D.map (MulAut.conj y).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hDcard]
  have hDA₁ : D.map (MulAut.conj y).toMonoidHom ≤ A := by
    intro z hz
    rw [mem_map_conj] at hz
    have h2 := (hyA' (y⁻¹ * z * y)).1 (hDA hz)
    simpa [mul_assoc] using h2
  have haD₁ : a ∈ D.map (MulAut.conj y).toMonoidHom := mem_map_conj.2 hay
  have hD₁ : D.map (MulAut.conj y).toMonoidHom ≠ E ⊓ A := by
    intro h
    apply haA0
    rw [← h]
    exact haD₁
  have hAT₁ : A ≤ Subgroup.normalizer ((T.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hx' : y⁻¹ * x * y ∈ A := by
      have := (hyA' (y⁻¹ * x * y)).2 (by simpa [mul_assoc] using hx)
      exact this
    have key := Subgroup.mem_normalizer_iff.1 (hAT hx') (y⁻¹ * z * y)
    rw [mem_map_conj, mem_map_conj]
    have e1 : (y⁻¹ * x * y) * (y⁻¹ * z * y) * (y⁻¹ * x * y)⁻¹ = y⁻¹ * (x * z * x⁻¹) * y := by
      group
    rw [e1] at key
    exact key
  have hmain := partB_aD (M := M) (E := E) (A := A) (T := T.map (MulAut.conj y).toMonoidHom)
    (D := D.map (MulAut.conj y).toMonoidHom) (a := a) hAM hAel hA27 hAmax hA0el hA0card hCa ha hF3 h112
    hnotD (by rw [hT₁card]; exact hT) hAT₁ hDA₁ hD₁card hD₁ haD₁
  intro x hx
  obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.1 hx
  have hzT : y * x * y⁻¹ ∈ T.map (MulAut.conj y).toMonoidHom := by
    rw [mem_map_conj]
    simpa [mul_assoc] using hxT
  have hzC : y * x * y⁻¹ ∈ Subgroup.centralizer ((D.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    rw [SetLike.mem_coe, mem_map_conj] at hd
    have hcomm : (y⁻¹ * d * y) * x = x * (y⁻¹ * d * y) := by
      have := Subgroup.mem_centralizer_iff.1 hxC (y⁻¹ * d * y) (by exact_mod_cast hd)
      exact this
    calc d * (y * x * y⁻¹) = y * ((y⁻¹ * d * y) * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * d * y)) * y⁻¹ := by rw [hcomm]
      _ = (y * x * y⁻¹) * d := by group
  have hzM := hmain (Subgroup.mem_inf.2 ⟨hzT, hzC⟩)
  have hx_eq : x = y⁻¹ * (y * x * y⁻¹) * y := by group
  rw [hx_eq]
  exact M.mul_mem (M.mul_mem (M.inv_mem hyM) hzM) hyM

theorem glbConj_zpowers (g x : G) : GLBConj g (Subgroup.zpowers x) = Subgroup.zpowers (g⁻¹ * x * g) := by
  unfold GLBConj
  rw [MonoidHom.map_zpowers]
  congr 1
  simp [mul_assoc]

theorem normalizes_of_commute {A A₀ : Subgroup G} {a n : G} (hAel : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hA₀A : A₀ ≤ A) (hA₀card : Nat.card ↥A₀ = 9) (ha : a ∈ A) (ha1 : a ≠ 1)
    (haA₀ : a ∉ A₀) (hna : Commute n a) (hnA₀ : n ∈ Subgroup.normalizer (A₀ : Set G)) :
    n ∈ Subgroup.normalizer (A : Set G) := by
  have key : ∀ m : G, Commute m a → m ∈ Subgroup.normalizer (A₀ : Set G) → ∀ x ∈ A, m * x * m⁻¹ ∈ A := by
    intro m hm hmN x hx
    obtain ⟨x₀, hx₀, i, _, rfl⟩ := coord_decomp hAel hA27 hA₀A hA₀card ha ha1 haA₀ hx
    have h1 : m * x₀ * m⁻¹ ∈ A₀ := (Subgroup.mem_normalizer_iff.1 hmN x₀).1 hx₀
    have h2 : m * a ^ i * m⁻¹ = a ^ i := by
      have hmi : Commute m (a ^ i) := hm.pow_right i
      rw [mul_inv_eq_iff_eq_mul, hmi.eq]
    have : m * (x₀ * a ^ i) * m⁻¹ = (m * x₀ * m⁻¹) * (m * a ^ i * m⁻¹) := by group
    rw [this, h2]
    exact A.mul_mem (hA₀A h1) (A.pow_mem ha i)
  refine Subgroup.mem_normalizer_iff.2 fun z => ⟨fun hz => key n hna hnA₀ z hz, fun hz => ?_⟩
  have h := key n⁻¹ hna.inv_left (Subgroup.inv_mem _ hnA₀) (n * z * n⁻¹) hz
  simpa [mul_assoc] using h

theorem normal_of_not_alpha {M E A D K : Subgroup G} {a a₁ : G}
    (hAel : IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hA0card : Nat.card ((E ⊓ A : Subgroup G)) = 9)
    (ha : a ∈ A) (ha1 : a ≠ 1) (haA0 : a ∉ E ⊓ A)
    (hKa : ∀ n ∈ K, Commute n a)
    (hF1 : ∀ x ∈ E ⊓ A, x ≠ 1 → ∀ y ∈ E ⊓ A, y ≠ 1 →
      ∃ n ∈ K, n ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ∧ n⁻¹ * x * n = y)
    (hNM : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M)
    (h1112iii : ∀ U : Subgroup G, IsEkIn 3 1 A U → (¬ U ≤ E ⊓ A ↔ GConj (Subgroup.zpowers a) U))
    (haD : a ∉ D) (hDA : D ≤ A) (ha₁D : a₁ ∈ D) (ha₁A₀ : a₁ ∉ E ⊓ A)
    (hnot : ∀ y ∈ M ⊓ Subgroup.normalizer (A : Set G), y⁻¹ * a * y ∉ D) :
    ∀ y ∈ M ⊓ Subgroup.normalizer (A : Set G), y⁻¹ * a * y ∈ Subgroup.zpowers a := by
  intro y hy
  obtain ⟨hyM, hyN⟩ := Subgroup.mem_inf.1 hy
  by_contra hcon
  have ha3 : a ^ 3 = 1 := hAel.2 a ha
  have hA₀A : E ⊓ A ≤ A := inf_le_right
  have hcA : y⁻¹ * a * y ∈ A :=
    (Subgroup.mem_normalizer_iff.1 hyN (y⁻¹ * a * y)).2 (by simpa [mul_assoc] using ha)
  have hne1 : y⁻¹ * a * y ≠ 1 := by
    intro h1
    apply ha1
    have : a = y * (y⁻¹ * a * y) * y⁻¹ := by group
    rw [this, h1]
    group
  have hconjpow : ∀ m : ℕ, (y⁻¹ * a * y) ^ m = y⁻¹ * a ^ m * y := by
    intro m
    induction m with
    | zero => group
    | succ m ih => rw [pow_succ, ih, pow_succ]; group
  have pow3 : (y⁻¹ * a * y) ^ 3 = 1 := by
    rw [hconjpow 3, ha3]
    group
  have hcA0 : y⁻¹ * a * y ∉ E ⊓ A := by
    intro hc
    have hIE : IsEkIn 3 1 A (Subgroup.zpowers (y⁻¹ * a * y)) :=
      ⟨Subgroup.zpowers_le.2 hcA, CFSG.Open.isElemAbelian_zpowers pow3, by
        rw [Nat.card_zpowers, orderOf_eq_prime pow3 hne1]
        norm_num⟩
    have hG : GConj (Subgroup.zpowers a) (Subgroup.zpowers (y⁻¹ * a * y)) := ⟨y, glbConj_zpowers y a⟩
    exact ((h1112iii _ hIE).2 hG) (Subgroup.zpowers_le.2 hc)
  obtain ⟨x_c, hx_c, k, hk, hck⟩ := coord_decomp hAel hA27 hA₀A hA0card ha ha1 haA0 hcA
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hcA0
    rw [hck, pow_zero, mul_one]
    exact hx_c
  have hxc1 : x_c ≠ 1 := by
    rintro rfl
    apply hcon
    rw [hck, one_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) k
  obtain ⟨x_1, hx_1, j, hj, ha₁eq⟩ := coord_decomp hAel hA27 hA₀A hA0card ha ha1 haA0
    (hDA ha₁D)
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply ha₁A₀
    rw [ha₁eq, pow_zero, mul_one]
    exact hx_1
  have hx11 : x_1 ≠ 1 := by
    rintro rfl
    rw [one_mul] at ha₁eq
    apply haD
    rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
    · rw [pow_one] at ha₁eq
      rw [← ha₁eq]
      exact ha₁D
    · have h4 : a ^ 2 * a ^ 2 = a := by
        rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, ha3, one_mul, pow_one]
      have h := D.mul_mem ha₁D ha₁D
      rw [ha₁eq, h4] at h
      exact h
  have hzD : ∃ z ∈ E ⊓ A, z ≠ 1 ∧ z * a ^ k ∈ D := by
    rcases (show k = j ∨ k + j = 3 by omega) with hkj | hkj
    · refine ⟨x_1, hx_1, hx11, ?_⟩
      rw [hkj, ← ha₁eq]
      exact ha₁D
    · refine ⟨x_1⁻¹, (E ⊓ A).inv_mem hx_1, inv_ne_one.2 hx11, ?_⟩
      have hak : a ^ k = (a ^ j)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_add, hkj, ha3]
      have hcomm : x_1 * a ^ j = a ^ j * x_1 :=
        elemAb_comm hAel (hA₀A hx_1) (A.pow_mem ha j)
      have hinv : x_1⁻¹ * a ^ k = (x_1 * a ^ j)⁻¹ := by
        rw [hak, mul_inv_rev]
        exact (show Commute x_1 (a ^ j) from hcomm).inv_inv.eq
      rw [hinv, ← ha₁eq]
      exact D.inv_mem ha₁D
  obtain ⟨z, hz_mem, hz1, hzD'⟩ := hzD
  obtain ⟨n, hnK, hnN, hn⟩ := hF1 x_c hx_c hxc1 z hz_mem hz1
  have hcm : n * a ^ k = a ^ k * n := ((hKa n hnK).pow_right k).eq
  have hnak : n⁻¹ * a ^ k * n = a ^ k := by
    calc n⁻¹ * a ^ k * n = n⁻¹ * (a ^ k * n) := by group
      _ = n⁻¹ * (n * a ^ k) := by rw [hcm]
      _ = a ^ k := by group
  have hnA : n ∈ Subgroup.normalizer (A : Set G) :=
    normalizes_of_commute hAel hA27 hA₀A hA0card ha ha1 haA0 (hKa n hnK) hnN
  have hy' : y * n ∈ M ⊓ Subgroup.normalizer (A : Set G) :=
    Subgroup.mem_inf.2 ⟨M.mul_mem hyM (hNM hnN), Subgroup.mul_mem _ hyN hnA⟩
  apply hnot (y * n) hy'
  have e1 : (y * n)⁻¹ * a * (y * n) = n⁻¹ * (y⁻¹ * a * y) * n := by group
  rw [e1, hck, show n⁻¹ * (x_c * a ^ k) * n = (n⁻¹ * x_c * n) * (n⁻¹ * a ^ k * n) by group, hn,
    hnak]
  exact hzD'

theorem not_normalizes_a1 {M E A K : Subgroup G} {a a₁ x₁ : G} {j : ℕ}
    (hAel : IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hA0card : Nat.card ((E ⊓ A : Subgroup G)) = 9)
    (ha : a ∈ A) (ha1 : a ≠ 1) (haA0 : a ∉ E ⊓ A)
    (hKa : ∀ n ∈ K, Commute n a)
    (hF1 : ∀ x ∈ E ⊓ A, x ≠ 1 → ∀ y ∈ E ⊓ A, y ≠ 1 →
      ∃ n ∈ K, n ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ∧ n⁻¹ * x * n = y)
    (hNM : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M)
    (hx1A₀ : x₁ ∈ E ⊓ A) (hx11 : x₁ ≠ 1) (ha₁eq : a₁ = x₁ * a ^ j) (hj : j < 3) (hj0 : j ≠ 0) :
    ¬ (M ⊓ Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer ((Subgroup.zpowers a₁ : Subgroup G) : Set G)) := by
  intro hN
  have ha3 : a ^ 3 = 1 := hAel.2 a ha
  have hA₀A : E ⊓ A ≤ A := inf_le_right
  obtain ⟨hbot, _⟩ := coord_setup hAel hA27 hA₀A hA0card ha ha1 haA0
  have hx13 : x₁ ^ 3 = 1 := hAel.2 x₁ (hA₀A hx1A₀)
  obtain ⟨y₀, hy₀A, hy₀⟩ : ∃ y₀ ∈ E ⊓ A, y₀ ∉ Subgroup.zpowers x₁ := by
    by_contra hcon
    push Not at hcon
    have hle : (E ⊓ A : Subgroup G) ≤ Subgroup.zpowers x₁ := fun z hz => hcon z hz
    have h3 : Nat.card ↥(Subgroup.zpowers x₁) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hx13 hx11]
    have := Subgroup.card_le_of_le hle
    omega
  have hy₀1 : y₀ ≠ 1 := by
    rintro rfl
    exact hy₀ (Subgroup.one_mem _)
  have hy₀x : y₀ ≠ x₁ := by
    rintro rfl
    exact hy₀ (Subgroup.mem_zpowers _)
  obtain ⟨n, hnK, hnN, hn⟩ := hF1 x₁ hx1A₀ hx11 y₀ hy₀A hy₀1
  have hnM : n ∈ M := hNM hnN
  have hcm : n * a ^ j = a ^ j * n := ((hKa n hnK).pow_right j).eq
  have hnaj : n⁻¹ * a ^ j * n = a ^ j := by
    calc n⁻¹ * a ^ j * n = n⁻¹ * (a ^ j * n) := by group
      _ = n⁻¹ * (n * a ^ j) := by rw [hcm]
      _ = a ^ j := by group
  have hm_norm : n⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.inv_mem _ (normalizes_of_commute hAel hA27 hA₀A hA0card ha ha1 haA0 (hKa n hnK) hnN)
  have hmM : n⁻¹ ∈ M ⊓ Subgroup.normalizer (A : Set G) :=
    Subgroup.mem_inf.2 ⟨M.inv_mem hnM, hm_norm⟩
  have hmem := (Subgroup.mem_normalizer_iff.1 (hN hmM) a₁).1 (Subgroup.mem_zpowers a₁)
  have hconj : n⁻¹ * a₁ * n⁻¹⁻¹ = y₀ * a ^ j := by
    rw [inv_inv, ha₁eq]
    have : n⁻¹ * (x₁ * a ^ j) * n = (n⁻¹ * x₁ * n) * (n⁻¹ * a ^ j * n) := by group
    rw [this, hnaj, hn]
  have hmem' : y₀ * a ^ j ∈ Subgroup.zpowers a₁ := by
    rw [← hconj]
    exact (Subgroup.mem_normalizer_iff.1 (hN hmM) a₁).1 (Subgroup.mem_zpowers a₁)
  have hpow_ne : ∀ i : ℕ, 0 < i → i < 3 → a ^ i ≠ 1 := by
    intro i hi0 hi3 h
    have := orderOf_dvd_of_pow_eq_one h
    rw [orderOf_eq_prime ha3 ha1] at this
    omega
  have hbotA : ∀ z : G, z ∈ E ⊓ A → z ∈ Subgroup.zpowers a → z = 1 := by
    intro z hzA hza
    have : z ∈ E ⊓ A ⊓ Subgroup.zpowers a := Subgroup.mem_inf.2 ⟨hzA, hza⟩
    rw [hbot] at this
    exact (Subgroup.mem_bot).1 this
  have hajA : a ^ j ∉ E ⊓ A := by
    intro h
    exact hpow_ne j (Nat.pos_of_ne_zero hj0) hj (hbotA _ h (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) j))
  have ha₁A : a₁ ∈ A := by
    rw [ha₁eq]
    exact A.mul_mem (hA₀A hx1A₀) (A.pow_mem ha j)
  have hcomm : Commute x₁ (a ^ j) := elemAb_comm hAel (hA₀A hx1A₀) (A.pow_mem ha j)
  have ha₁3 : a₁ ^ 3 = 1 := hAel.2 a₁ ha₁A
  have ha₁1 : a₁ ≠ 1 := by
    intro h
    rw [ha₁eq] at h
    have hx : a ^ j = x₁⁻¹ := eq_inv_of_mul_eq_one_right h
    apply hajA
    rw [hx]
    exact (E ⊓ A).inv_mem hx1A₀
  have hwrap : ∃ r : ℕ, r < 3 ∧ a₁ ^ r = y₀ * a ^ j := by
    obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.1 hmem'
    have hmod : a₁ ^ (t % (3 : ℤ)) = a₁ ^ t := by
      have := zpow_mod_orderOf a₁ t
      rwa [orderOf_eq_prime ha₁3 ha₁1] at this
    have h0 : 0 ≤ t % (3 : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h1 : t % (3 : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
    refine ⟨(t % (3 : ℤ)).toNat, by omega, ?_⟩
    rw [← zpow_natCast, Int.toNat_of_nonneg h0, hmod, ht]
  obtain ⟨r, hr3, hr⟩ := hwrap
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl
  ·
    rw [pow_zero] at hr
    apply hajA
    have hx : a ^ j = y₀⁻¹ := eq_inv_of_mul_eq_one_right hr.symm
    rw [hx]
    exact (E ⊓ A).inv_mem hy₀A
  ·
    rw [pow_one, ha₁eq] at hr
    exact hy₀x (mul_right_cancel hr).symm
  ·
    have h2 : x₁ ^ 2 * (a ^ j) ^ 2 = a₁ ^ 2 := by
      rw [ha₁eq]
      exact (hcomm.mul_pow 2).symm
    have h3 : x₁ ^ 2 * (a ^ j) ^ 2 = y₀ * a ^ j := h2.trans hr
    apply hajA
    have hx : a ^ j = (x₁ ^ 2)⁻¹ * y₀ := by
      calc a ^ j = (x₁ ^ 2)⁻¹ * (x₁ ^ 2 * (a ^ j) ^ 2) * (a ^ j)⁻¹ := by group
        _ = (x₁ ^ 2)⁻¹ * (y₀ * a ^ j) * (a ^ j)⁻¹ := by rw [h3]
        _ = (x₁ ^ 2)⁻¹ * y₀ := by group
    rw [hx]
    exact (E ⊓ A).mul_mem ((E ⊓ A).inv_mem ((E ⊓ A).pow_mem hx1A₀ 2)) hy₀A

theorem glbConj_centralizer_singleton (g a : G) :
    GLBConj g (Subgroup.centralizer ({a} : Set G)) = Subgroup.centralizer ({g⁻¹ * a * g} : Set G) := by
  ext x
  unfold GLBConj
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * (g⁻¹ * a * g) = g⁻¹ * (g * x * g⁻¹ * a) * g := by group
      _ = g⁻¹ * (a * (g * x * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * a * g * x := by group
  · intro h
    calc g * x * g⁻¹ * a = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by rw [h]
      _ = a * (g * x * g⁻¹) := by group

theorem centralizer_singleton_eq_of_zpowers_eq {b c : G} (h : Subgroup.zpowers b = Subgroup.zpowers c) :
    Subgroup.centralizer ({b} : Set G) = Subgroup.centralizer ({c} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hb : b ∈ Subgroup.zpowers c := h ▸ Subgroup.mem_zpowers b
  have hc : c ∈ Subgroup.zpowers b := h.symm ▸ Subgroup.mem_zpowers c
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc
    have := (show Commute x b from hx).zpow_right k
    rw [hk] at this
    exact this
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hb
    have := (show Commute x c from hx).zpow_right k
    rw [hk] at this
    exact this

theorem isLThreeFour_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsLThreeFour X) : IsLThreeFour Y := by
  obtain ⟨K, hf, hfin, hc, ⟨φ⟩⟩ := h
  exact ⟨K, hf, hfin, hc, ⟨e.symm.trans φ⟩⟩

theorem isLThreeFour_center_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsLThreeFour (X ⧸ Subgroup.center X)) : IsLThreeFour (Y ⧸ Subgroup.center Y) :=
  isLThreeFour_of_mulEquiv (QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e
    (Subgroup.map_center_eq e)) h

theorem K1_le_M {m : ℕ} {B M E A K : Subgroup G} {a a₁ : G} (h : Cex117 G m 3 B M E A a K)
    (hIL : IsLThreeFour (barOf 3 K))
    (hNa : NormalizesCyc M A a) (ha₁A : a₁ ∈ A) (ha₁A₀ : a₁ ∉ E ⊓ A)
    (hnorm1 : ¬ NormalizesCyc M A a₁)
    (hGC : GConj (Subgroup.zpowers a) (Subgroup.zpowers a₁)) :
    ∃ K₁ : Subgroup G, GLAPComponent 3 (Subgroup.centralizer ({a₁} : Set G)) K₁ ∧
      IsLThreeFour (barOf 3 K₁) ∧ K₁ ≤ M := by
  obtain ⟨g, hg⟩ := hGC
  set b := g⁻¹ * a * g with hb
  have hbz : Subgroup.zpowers b = Subgroup.zpowers a₁ := by
    rw [hb, ← glbConj_zpowers, hg]
  have hCb : GLBConj g (Subgroup.centralizer ({a} : Set G)) = Subgroup.centralizer ({b} : Set G) :=
    glbConj_centralizer_singleton g a
  have hCa₁ : Subgroup.centralizer ({b} : Set G) = Subgroup.centralizer ({a₁} : Set G) :=
    centralizer_singleton_eq_of_zpowers_eq hbz
  have hKb : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) (GLBConj g K) := by
    rw [← hCb]
    exact CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj h.hK g
  have hK₁a₁ : GLAPComponent 3 (Subgroup.centralizer ({a₁} : Set G)) (GLBConj g K) := by
    rw [← hCa₁]
    exact hKb
  have hiso : barOf 3 K ≃* barOf 3 (GLBConj g K) := conjQuotEquiv 3 g K
  have hIL₁ : IsLThreeFour (barOf 3 (GLBConj g K)) := isLThreeFour_of_mulEquiv hiso hIL
  refine ⟨GLBConj g K, hK₁a₁, hIL₁, ?_⟩
  by_contra hKM
  have hbA : b ∈ A := by
    have h1 : Subgroup.zpowers b ≤ A := by
      rw [hbz]
      exact Subgroup.zpowers_le.2 ha₁A
    exact Subgroup.zpowers_le.1 h1
  have hb1 : b ≠ 1 := by
    intro h1
    apply h.ha.2
    have hab : a = g * b * g⁻¹ := by rw [hb]; group
    rw [hab, h1]
    group
  have ht₁ : Type117a 3 E A (GLBConj g K) ∨ Type117b 3 (GLBConj g K) ∨
      Type117c 3 A (GLBConj g K) := by
    rcases h.ht with ⟨n, hn, hpn, hdn⟩ | ⟨h5, _⟩ | ⟨_, hA3, hL⟩
    · exact Or.inl ⟨n, hn.elim fun φ => ⟨hiso.symm.trans φ⟩, hpn, hdn⟩
    · exact absurd h5 (by norm_num)
    · exact Or.inr (Or.inr ⟨rfl, hA3, isLThreeFour_center_of_mulEquiv hiso hL⟩)
  have hnotD : ¬ ∃ A₁ : Subgroup G, inD 3 M A₁ ∧ b ∈ A₁ := by
    rintro ⟨A₁, hA₁, hbA₁⟩
    exact hKM (hA₁.2.clause_e rfl b hbA₁ hb1 (GLBConj g K) hKb (Or.inl hIL₁))
  let cexb : Cex117Base G m 3 B M E A b (GLBConj g K) :=
    { toSec11 := h.toCex117Base.toSec11
      ha := ⟨hbA, hb1⟩
      hK := hKb
      ht := ht₁
      notM := hKM
      notD := hnotD }
  have hnb : ¬ NormalizesCyc M A b := by
    unfold NormalizesCyc at hnorm1 ⊢
    rw [hbz]
    exact hnorm1
  exact h.choice ⟨E, A, b, GLBConj g K, cexb, hnb⟩ hNa

theorem zpowers_conj_le {y a : G} (h2 : y * a * y⁻¹ ∈ Subgroup.zpowers a) {z : G}
    (hz : z ∈ Subgroup.zpowers a) : y * z * y⁻¹ ∈ Subgroup.zpowers a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hk : y * a ^ k * y⁻¹ = (y * a * y⁻¹) ^ k := by
    have := map_zpow (MulAut.conj y) a k
    simpa [MulAut.conj_apply] using this.symm
  rw [hk]
  exact Subgroup.zpow_mem _ h2 k

theorem normalizes_zpowers_of_conj {y a : G} (h1 : y⁻¹ * a * y ∈ Subgroup.zpowers a)
    (h2 : y * a * y⁻¹ ∈ Subgroup.zpowers a) :
    y ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact zpowers_conj_le h2
  · intro hz
    have h1' : y⁻¹ * a * y⁻¹⁻¹ ∈ Subgroup.zpowers a := by rw [inv_inv]; exact h1
    have h2' : y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z := by group
    have := zpowers_conj_le (y := y⁻¹) (a := a) h1' hz
    rwa [h2'] at this

theorem centralizer_le_normalizer_set (X : Subgroup G) :
    Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hc := Subgroup.mem_centralizer_iff.1 hx h hh
    have e : x * h * x⁻¹ = h := by
      rw [← hc]
      group
    rw [e]
    exact hh
  · intro hh
    have hc := Subgroup.mem_centralizer_iff.1 hx (x * h * x⁻¹) hh
    have h2 : x * h = x * (x * h * x⁻¹) := (show x * h = x * h * x⁻¹ * x by group).trans hc
    have e : h = x * h * x⁻¹ := mul_left_cancel h2
    rw [e]
    exact hh

theorem centralizer_le_of_normalizer_le {M X : Subgroup G} (hNM : Subgroup.normalizer (X : Set G) ≤ M) :
    Subgroup.centralizer (X : Set G) ≤ M :=
  (centralizer_le_normalizer_set X).trans hNM

theorem coord_x1_ne_one {D : Subgroup G} {a a₁ x₁ : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (haD : a ∉ D) (ha₁D : a₁ ∈ D) {j : ℕ} (hj0 : j ≠ 0) (hj : j < 3)
    (ha₁eq : a₁ = x₁ * a ^ j) : x₁ ≠ 1 := by
  rintro rfl
  rw [one_mul] at ha₁eq
  apply haD
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
  · rw [pow_one] at ha₁eq
    rw [← ha₁eq]
    exact ha₁D
  · have h4 : a ^ 2 * a ^ 2 = a := by
      rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, ha3, one_mul, pow_one]
    have h := D.mul_mem ha₁D ha₁D
    rw [ha₁eq, h4] at h
    exact h

theorem partB_core {m : ℕ} {B M E A K : Subgroup G} {a : G} (h : Cex117 G m 3 B M E A a K)
    (hIL : IsLThreeFour (barOf 3 K))
    (hAM : A ≤ M) (hAel : IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAmax : ∀ F : Subgroup G, F ≤ M → IsElemAbelian 3 F → A ≤ F → F = A)
    (hA0el : IsElemAbelian 3 (E ⊓ A : Subgroup G)) (hA0card : Nat.card ((E ⊓ A : Subgroup G)) = 9)
    (hCa : CFSG.Open.pRank 3 (Subgroup.centralizer ({a} : Set G)) = 3)
    (ha : a ∈ A) (ha1 : a ≠ 1) (haA0 : a ∉ E ⊓ A)
    (hKa : ∀ n ∈ K, Commute n a)
    (hF1 : ∀ x ∈ E ⊓ A, x ≠ 1 → ∀ y ∈ E ⊓ A, y ≠ 1 →
      ∃ n ∈ K, n ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ∧ n⁻¹ * x * n = y)
    (hNM : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M)
    (hF2 : ∀ a₁ ∈ A, a₁ ∉ E ⊓ A → ∀ K₁ : Subgroup G, GLAPComponent 3 (Cg a₁) K₁ →
      IsLThreeFour (barOf 3 K₁) →
      ∀ S : Subgroup G, S ≤ Cg a₁ → ¬ 3 ∣ Nat.card S → A ≤ Subgroup.normalizer (S : Set G) →
        S ≤ K₁ ⊔ GLAPPrimeCoreOf 3 (Cg a₁) ⊔ Subgroup.centralizer (A : Set G))
    (hF3 : ∀ e ∈ E ⊓ A, e ≠ 1 → GLAPLayer 3 (Subgroup.centralizer ({e, a} : Set G)) = ⊥)
    (h112 : ∀ e ∈ E ⊓ A, e ≠ 1 → GLAPPrimeCoreOf 3 (Subgroup.centralizer ({e, a} : Set G)) ≤ M ∨
      ∃ A₁ : Subgroup G, inD 3 M A₁ ∧ a ∈ A₁)
    (h111 : ∀ b ∈ A, b ≠ 1 → GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ≤ M)
    (h1112iii : ∀ U : Subgroup G, IsEkIn 3 1 A U → (¬ U ≤ E ⊓ A ↔ GConj (Subgroup.zpowers a) U))
    (hnotD : ¬ ∃ A₁ : Subgroup G, inD 3 M A₁ ∧ a ∈ A₁)
    {T D : Subgroup G} (hDA : D ≤ A) (hDcard : Nat.card D = 9) (hD : D ≠ E ⊓ A)
    (hT : ¬ 3 ∣ Nat.card T) (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    T ⊓ Subgroup.centralizer (D : Set G) ≤ M := by
  have ha3 : a ^ 3 = 1 := hAel.2 a ha
  have hA₀A : E ⊓ A ≤ A := inf_le_right
  by_cases haD : a ∈ D
  · exact partB_aD hAM hAel hA27 hAmax hA0el hA0card hCa ha hF3 h112 hnotD hT hAT hDA hDcard hD haD
  by_cases hα : ∃ y ∈ M ⊓ Subgroup.normalizer (A : Set G), y⁻¹ * a * y ∈ D
  · obtain ⟨y, hy, hyD⟩ := hα
    obtain ⟨hyM, hyN⟩ := Subgroup.mem_inf.1 hy
    exact partB_alpha hAM hAel hA27 hAmax hA0el hA0card hCa ha haA0 hF3 h112 hnotD hyM hyN hyD hT hAT
      hDA hDcard
  push Not at hα
  obtain ⟨a₁, ha₁D, ha₁A₀⟩ : ∃ a₁ ∈ D, a₁ ∉ E ⊓ A := by
    by_contra hcon
    push Not at hcon
    exact hD (Subgroup.eq_of_le_of_card_ge (fun d hd => hcon d hd) (by omega))
  have ha₁A : a₁ ∈ A := hDA ha₁D
  have hN := normal_of_not_alpha hAel hA27 hA0card ha ha1 haA0 hKa hF1 hNM h1112iii haD hDA ha₁D
    ha₁A₀ hα
  have hNa : NormalizesCyc M A a := by
    intro y hy
    have hy' := hN y hy
    have hy'' := hN y⁻¹ (Subgroup.inv_mem _ hy)
    rw [inv_inv] at hy''
    exact normalizes_zpowers_of_conj hy' hy''
  obtain ⟨x_1, hx_1, j, hj, ha₁eq⟩ := coord_decomp hAel hA27 hA₀A hA0card ha ha1 haA0 ha₁A
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply ha₁A₀
    rw [ha₁eq, pow_zero, mul_one]
    exact hx_1
  have hx11 : x_1 ≠ 1 := coord_x1_ne_one ha3 ha1 haD ha₁D hj0 hj ha₁eq
  have hnotN := not_normalizes_a1 hAel hA27 hA0card ha ha1 haA0 hKa hF1 hNM hx_1 hx11 ha₁eq hj hj0
  have ha₁1 : a₁ ≠ 1 := by
    intro h1
    apply ha₁A₀
    rw [h1]
    exact (E ⊓ A).one_mem
  have hIE : IsEkIn 3 1 A (Subgroup.zpowers a₁) :=
    ⟨Subgroup.zpowers_le.2 ha₁A, CFSG.Open.isElemAbelian_zpowers (hAel.2 a₁ ha₁A), by
      rw [Nat.card_zpowers, orderOf_eq_prime (hAel.2 a₁ ha₁A) ha₁1]
      norm_num⟩
  have hnotle : ¬ Subgroup.zpowers a₁ ≤ E ⊓ A := fun hle => ha₁A₀ (Subgroup.zpowers_le.1 hle)
  have hGC : GConj (Subgroup.zpowers a) (Subgroup.zpowers a₁) := (h1112iii _ hIE).1 hnotle
  obtain ⟨K₁, hK₁comp, hIL₁, hK₁M⟩ := K1_le_M h hIL hNa ha₁A ha₁A₀ hnotN hGC
  have hS_le : T ⊓ Subgroup.centralizer (D : Set G) ≤ Cg a₁ :=
    (inf_le_right).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 ha₁D))
  have hcopS : ¬ 3 ∣ Nat.card ((T ⊓ Subgroup.centralizer (D : Set G) : Subgroup G)) := fun hd =>
    hT (hd.trans (Subgroup.card_dvd_of_le
      (inf_le_left : (T ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) ≤ T)))
  have hAS : A ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_centralizer_set hAT (fun x hx s hs => elemAb_comm hAel hx (hDA hs))
  have hSM := hF2 a₁ ha₁A ha₁A₀ K₁ hK₁comp hIL₁ _ hS_le hcopS hAS
  have hCAM : Subgroup.centralizer (A : Set G) ≤ M := by
    refine le_trans (Subgroup.centralizer_le ?_) (centralizer_le_of_normalizer_le hNM)
    intro x hx
    exact (Subgroup.mem_inf.1 hx).2
  exact hSM.trans (sup_le (sup_le hK₁M (h111 a₁ ha₁A ha₁1)) hCAM)

theorem _root_.CFSG.LocalAnalysis.GLTheoremB.MovingAround.lemma1114_of_inputs
    (h1111 : Lemma1111Statement) (h119 : Lemma119Statement) (h1112 : Lemma1112Statement)
    (h1113 : Lemma1113Statement) (h111 : Prop111Statement) (h112 : Prop112Statement)
    (hF1 : Lemma1114FusionInput) (hF2 : Lemma1114ChiefInput) (hF3 : Lemma1114ConstrInput) :
    Lemma1114Statement := by
  intro G _ _ m p B M E A a K h
  obtain ⟨rfl, hA3, hIL⟩ := h1111 h
  have hsec : Sec11 G m 3 B M E A := h.toCex117Base.toSec11
  have hE : inD 3 M E := hsec.pair.1.1
  have hAp : inDp 3 M A := hsec.pair.1.2.1
  have hA0 : CFSG.Open.pRank 3 (E ⊓ A) = 2 := (h119 h).1
  have hAM : A ≤ M := hAp.1.1.1
  have hAel : IsElemAbelian 3 A := hAp.1.1.2.1
  have hAmax : ∀ F : Subgroup G, F ≤ M → IsElemAbelian 3 F → A ≤ F → F = A :=
    fun F hF hFe hAF => hAp.1.1.2.2 F hF hFe hAF
  have hA27 : Nat.card A = 27 := card_eq_27_of_pRank hAel hA3
  have hA0el : IsElemAbelian 3 (E ⊓ A : Subgroup G) :=
    CFSG.Open.IsElemAbelian.mono hAel inf_le_right
  have hA0card : Nat.card ((E ⊓ A : Subgroup G)) = 9 := by
    rw [card_eq_pow_of_pRank hA0el, hA0]
    norm_num
  have ha : a ∈ A := h.ha.1
  have ha1 : a ≠ 1 := h.ha.2
  have hnotD : ¬ ∃ A₁ : Subgroup G, inD 3 M A₁ ∧ a ∈ A₁ := h.notD
  have haA0 : a ∉ E ⊓ A := fun haE => hnotD ⟨E, hE, (Subgroup.mem_inf.1 haE).1⟩
  obtain ⟨⟨_, hCa⟩, _, h1112iii⟩ := h1112 h
  have hKa : ∀ n ∈ K, Commute n a := by
    intro n hn
    exact Subgroup.mem_centralizer_singleton_iff.1 (h.hK.1 hn)
  have hNM : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M := by
    have hsub : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ GLBCore 3 2 E :=
      le_sSup ⟨E ⊓ A, inf_le_left, hA0.ge, rfl⟩
    exact hsub.trans hE.2.clause_d
  have hF1' := hF1 h rfl hIL
  have hF2' := hF2 h rfl hIL
  have hF3' := hF3 h rfl hIL
  have h112' : ∀ e ∈ E ⊓ A, e ≠ 1 → GLAPPrimeCoreOf 3 (Subgroup.centralizer ({e, a} : Set G)) ≤ M ∨
      ∃ A₁ : Subgroup G, inD 3 M A₁ ∧ a ∈ A₁ :=
    fun e he he1 => h112 hsec ha ha1 he he1
  have h111' : ∀ b ∈ A, b ≠ 1 → GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ≤ M :=
    fun b hb hb1 => h111 hsec hb hb1
  have h13 : ∀ e ∈ E ⊓ A, e ≠ 1 →
      GLAPLayer 3 (M ⊓ Subgroup.centralizer ({e} : Set G)) = ⊥ ∧
        GLAPPrimeCoreOf 3 (M ⊓ Subgroup.centralizer ({e} : Set G)) ≤ GLAPPrimeCoreOf 3 M :=
    fun e he he1 => h1113 h e he he1
  refine iSup₂_le fun T hT => ?_
  obtain ⟨-, hTcop, hAT⟩ := hT
  have hT3 : ¬ 3 ∣ Nat.card T := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hTcop
  have hA1 : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hA27
    norm_num at hA27
  have hTM : T ≤ M := by
    have hgen := gen_by_hyperplanes (p := 3) Nat.prime_three hAel hA1 hAT hT3
    refine hgen.trans (iSup₂_le fun D hD => ?_)
    obtain ⟨hDA, hDi⟩ := hD
    have hDc := card_of_index_three_gen hDA hA27 hDi
    have hDc' : Nat.card D = 9 := by omega
    by_cases hDA0 : D = E ⊓ A
    · rw [hDA0]
      exact inf_le_right.trans (centralizer_le_of_normalizer_le hNM)
    · exact partB_core h hIL hAM hAel hA27 hAmax hA0el hA0card hCa ha ha1 haA0 hKa hF1' hNM hF2' hF3'
        h112' h111' h1112iii hnotD hDA hDc' hDA0 hT3 hAT
  exact partA hAM hAel hAmax hA0 h13 hTM hT3 hAT

@[expose] def Lemma1115ChiefAInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (_h : Cex117 G m p B M E A a K), p = 3 → IsLThreeFour (barOf 3 K) →
    ⁅(pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G), A⁆ ≤ GLAPPrimeCoreOf 3 (Cg a)

@[expose] def Lemma1115CompInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (_h : Cex117 G m p B M E A a K), p = 3 → IsLThreeFour (barOf 3 K) →
    ∀ a₁ ∈ A, a₁ ∉ E ⊓ A → ∀ K₁ : Subgroup G, GLAPComponent 3 (Cg a₁) K₁ →
      IsLThreeFour (barOf 3 K₁) →
      (∀ g ∈ Cg a₁, ∀ k ∈ K₁, g * k * g⁻¹ ∈ K₁) ∧
        pCoreOf 2 (K₁ ⊔ GLAPPrimeCoreOf 3 (Cg a₁)) ≤ GLAPPrimeCoreOf 3 (Cg a₁)

theorem eq_bot_of_two_le_odd {X H : Subgroup G} (hH : IsPGroup 2 H) (hHX : H ≤ X)
    (hodd : Odd (Nat.card X)) : H = ⊥ := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hH
  have hdvd : Nat.card H ∣ Nat.card X := Subgroup.card_dvd_of_le hHX
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    exact Subgroup.eq_bot_of_card_eq H (by rw [hn]; norm_num)
  · exfalso
    have h2 : 2 ∣ Nat.card X := by
      refine dvd_trans ?_ hdvd
      rw [hn]
      exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.1 hpos)
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem le_pCoreOf_two_of_normal {Y W : Subgroup G} (hWY : W ≤ Y) (hP : IsPGroup 2 W)
    (hn : ∀ y ∈ Y, ∀ w ∈ W, y * w * y⁻¹ ∈ W) : W ≤ pCoreOf 2 Y := by
  have hWn : (W.subgroupOf Y).Normal := by
    refine ⟨fun n hn' g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    have := hn (g : G) g.2 n hn'
    simpa [Subgroup.mem_subgroupOf] using this
  have hPY : IsPGroup 2 (W.subgroupOf Y) := by
    intro x
    obtain ⟨k, hk⟩ := hP ⟨((x : Y) : G), Subgroup.mem_subgroupOf.1 x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  intro w hw
  have hwY : (⟨w, hWY hw⟩ : Y) ∈ W.subgroupOf Y := Subgroup.mem_subgroupOf.2 hw
  have hmem : W.subgroupOf Y ∈ {K : Subgroup ↥Y | K.Normal ∧ IsPGroup 2 K} := ⟨hWn, hPY⟩
  have hcore : (⟨w, hWY hw⟩ : Y) ∈ CFSG.pCore 2 ↥Y := by
    unfold CFSG.pCore
    exact le_sSup hmem hwY
  unfold pCoreOf
  exact Subgroup.mem_map.2 ⟨⟨w, hWY hw⟩, hcore, rfl⟩

theorem commutator_le_of_sup {C K₁ O' Y A : Subgroup G} (hAC : A ≤ C)
    (hKC : K₁ ≤ C) (hOC : O' ≤ C) (hCAC : Subgroup.centralizer (A : Set G) ≤ C)
    (hKn : ∀ g ∈ C, ∀ k ∈ K₁, g * k * g⁻¹ ∈ K₁) (hOn : ∀ g ∈ C, ∀ o ∈ O', g * o * g⁻¹ ∈ O')
    (hYn : ∀ g ∈ C, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) (hKY : K₁ ≤ Y) (hOY : O' ≤ Y)
    {S : Subgroup G} (hSZ : S ≤ K₁ ⊔ O' ⊔ Subgroup.centralizer (A : Set G)) :
    ⁅S, A⁆ ≤ Y := by
  let Q : Subgroup G :=
    { carrier := {g | g ∈ C ∧ ∀ x ∈ A, ⁅g, x⁆ ∈ Y}
      mul_mem' := by
        rintro g h ⟨hg, hgY⟩ ⟨hh, hhY⟩
        refine ⟨C.mul_mem hg hh, fun x hx => ?_⟩
        have e : ⁅g * h, x⁆ = g * ⁅h, x⁆ * g⁻¹ * ⁅g, x⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Y.mul_mem (hYn g hg _ (hhY x hx)) (hgY x hx)
      one_mem' := ⟨C.one_mem, fun x _ => by simp [Y.one_mem]⟩
      inv_mem' := by
        rintro g ⟨hg, hgY⟩
        refine ⟨C.inv_mem hg, fun x hx => ?_⟩
        have e : ⁅g⁻¹, x⁆ = g⁻¹ * (⁅g, x⁆)⁻¹ * g := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := hYn g⁻¹ (C.inv_mem hg) _ (Y.inv_mem (hgY x hx))
        rwa [inv_inv] at this }
  have hKQ : K₁ ≤ Q := by
    intro k hk
    refine ⟨hKC hk, fun x hx => ?_⟩
    have hxC : x ∈ C := hAC hx
    have h1 : x * k * x⁻¹ ∈ K₁ := hKn x hxC k hk
    have e : ⁅k, x⁆ = k * (x * k * x⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Y.mul_mem (hKY hk) (hKY (K₁.inv_mem h1))
  have hOQ : O' ≤ Q := by
    intro o ho
    refine ⟨hOC ho, fun x hx => ?_⟩
    have hxC : x ∈ C := hAC hx
    have h1 : x * o * x⁻¹ ∈ O' := hOn x hxC o ho
    have e : ⁅o, x⁆ = o * (x * o * x⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Y.mul_mem (hOY ho) (hOY (O'.inv_mem h1))
  have hCAQ : Subgroup.centralizer (A : Set G) ≤ Q := by
    intro z hz
    refine ⟨hCAC hz, fun x hx => ?_⟩
    have hzx : z * x = x * z := (Subgroup.mem_centralizer_iff.1 hz x hx).symm
    have e : ⁅z, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hzx
    rw [e]
    exact Y.one_mem
  have hZQ : K₁ ⊔ O' ⊔ Subgroup.centralizer (A : Set G) ≤ Q :=
    sup_le (sup_le hKQ hOQ) hCAQ
  rw [Subgroup.commutator_le]
  intro s hs g hg
  exact (hZQ (hSZ hs)).2 g hg

theorem glaPPrimeCoreOf_conj_mem' {p : ℕ} [Fact p.Prime] {H : Subgroup G} {g x : G} (hg : g ∈ H)
    (hx : x ∈ GLAPPrimeCoreOf p H) : g * x * g⁻¹ ∈ GLAPPrimeCoreOf p H := by
  unfold GLAPPrimeCoreOf at hx ⊢
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  have hN : (GLAPPrimeCore p ↥H).Normal := inferInstance
  refine Subgroup.mem_map.2 ⟨(⟨g, hg⟩ : H) * y * (⟨g, hg⟩ : H)⁻¹, hN.conj_mem y hy _, ?_⟩
  simp

theorem mem_GLBConj_iff {H : Subgroup G} {g x : G} : x ∈ GLBConj g H ↔ g * x * g⁻¹ ∈ H := by
  unfold GLBConj
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply, mul_assoc]

theorem pCoreOf_two_conj_mem {M : Subgroup G} {y t : G} (hy : y ∈ M) (ht : t ∈ pCoreOf 2 M) :
    y * t * y⁻¹ ∈ pCoreOf 2 M := by
  have hg : y⁻¹ ∈ M := M.inv_mem hy
  have hM : GLBConj y⁻¹ M = M := by
    ext x
    rw [mem_GLBConj_iff]
    constructor
    · intro h
      have := M.mul_mem (M.mul_mem hy h) hg
      simpa [mul_assoc] using this
    · intro h
      have := M.mul_mem (M.mul_mem hg h) hy
      simpa [mul_assoc] using this
  have h1 : GLBConj y⁻¹ (pCoreOf 2 M) = pCoreOf 2 M := by
    rw [← pCoreOf_gLBConj, hM]
  have hmem : y * t * y⁻¹ ∈ GLBConj y⁻¹ (pCoreOf 2 M) := mem_GLBConj_iff.2 (by
    simpa [mul_assoc] using ht)
  rw [h1] at hmem
  exact hmem

def PzProp (M A : Subgroup G) (x : G) : Prop :=
  ∀ t ∈ pCoreOf 2 M, t * x = x * t → ∀ b ∈ A, t * b = b * t

theorem commute_of_zpowers_eq {u v t : G} (h : Subgroup.zpowers u = Subgroup.zpowers v)
    (htu : t * u = u * t) : t * v = v * t := by
  have hv : v ∈ Subgroup.zpowers u := h ▸ Subgroup.mem_zpowers v
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hv
  have hc : Commute t (u ^ k) := (show Commute t u from htu).zpow_right k
  rw [hk] at hc
  exact hc

theorem pzProp_zpowers_eq {M A : Subgroup G} {x x' : G}
    (h : Subgroup.zpowers x = Subgroup.zpowers x') :
    PzProp M A x ↔ PzProp M A x' := by
  unfold PzProp
  constructor
  · intro H t ht htx b hb
    exact H t ht (commute_of_zpowers_eq h.symm htx) b hb
  · intro H t ht htx b hb
    exact H t ht (commute_of_zpowers_eq h htx) b hb

theorem pz_conj_imp {M A : Subgroup G} {x y : G} (hy : y ∈ M)
    (hyA : y ∈ Subgroup.normalizer (A : Set G)) (H : PzProp M A (y⁻¹ * x * y)) : PzProp M A x := by
  intro t ht htx b hb
  have hy' : y⁻¹ ∈ M := M.inv_mem hy
  have ht' : y⁻¹ * t * y⁻¹⁻¹ ∈ pCoreOf 2 M := pCoreOf_two_conj_mem hy' ht
  have hb' : y⁻¹ * b * y⁻¹⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hyA) b).1 hb
  have hc : (y⁻¹ * t * y⁻¹⁻¹) * (y⁻¹ * x * y) = (y⁻¹ * x * y) * (y⁻¹ * t * y⁻¹⁻¹) := by
    simp only [inv_inv]
    calc y⁻¹ * t * y * (y⁻¹ * x * y) = y⁻¹ * (t * x) * y := by group
      _ = y⁻¹ * (x * t) * y := by rw [htx]
      _ = y⁻¹ * x * y * (y⁻¹ * t * y) := by group
  have key := H _ ht' hc _ hb'
  simp only [inv_inv] at key
  calc t * b = y * ((y⁻¹ * t * y) * (y⁻¹ * b * y)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * b * y) * (y⁻¹ * t * y)) * y⁻¹ := by rw [key]
    _ = b * t := by group

theorem pz_conj {M A : Subgroup G} {x y : G} (hy : y ∈ M)
    (hyA : y ∈ Subgroup.normalizer (A : Set G)) : PzProp M A (y⁻¹ * x * y) ↔ PzProp M A x := by
  constructor
  · exact pz_conj_imp hy hyA
  · intro H
    have hy' : y⁻¹ ∈ M := M.inv_mem hy
    have hyA' : y⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ hyA
    have := pz_conj_imp (x := y⁻¹ * x * y) (y := y⁻¹) hy' hyA' (by
      simp only [inv_inv]
      rw [show y * (y⁻¹ * x * y) * y⁻¹ = x by group]
      exact H)
    simpa using this

theorem zpowers_conj_of_pz {M E A K : Subgroup G} {a a₁ x₁ : G} {j : ℕ}
    (hAel : IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hA0card : Nat.card ((E ⊓ A : Subgroup G)) = 9)
    (ha : a ∈ A) (ha1 : a ≠ 1) (haA0 : a ∉ E ⊓ A)
    (hKa : ∀ n ∈ K, Commute n a)
    (hF1 : ∀ x ∈ E ⊓ A, x ≠ 1 → ∀ y ∈ E ⊓ A, y ≠ 1 →
      ∃ n ∈ K, n ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ∧ n⁻¹ * x * n = y)
    (hNM : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M)
    (h1112iii : ∀ U : Subgroup G, IsEkIn 3 1 A U → (¬ U ≤ E ⊓ A ↔ GConj (Subgroup.zpowers a) U))
    (hPa : PzProp M A a) (hPa1 : ¬ PzProp M A a₁)
    (hx1A₀ : x₁ ∈ E ⊓ A) (hx11 : x₁ ≠ 1) (ha₁eq : a₁ = x₁ * a ^ j) (ha₁A : a₁ ∈ A)
    (ha₁A₀ : a₁ ∉ E ⊓ A) (hj : j < 3) (hj0 : j ≠ 0)
    {y : G} (hy : y ∈ M ⊓ Subgroup.normalizer (A : Set G)) : y⁻¹ * a * y ∈ Subgroup.zpowers a := by
  obtain ⟨hyM, hyN⟩ := Subgroup.mem_inf.1 hy
  by_contra hcon
  have ha3 : a ^ 3 = 1 := hAel.2 a ha
  have hA₀A : E ⊓ A ≤ A := inf_le_right
  have hcA : y⁻¹ * a * y ∈ A :=
    (Subgroup.mem_normalizer_iff.1 hyN (y⁻¹ * a * y)).2 (by simpa [mul_assoc] using ha)
  have hcA0 : y⁻¹ * a * y ∉ E ⊓ A := by
    intro hc
    have hne1 : y⁻¹ * a * y ≠ 1 := by
      intro h1
      apply ha1
      have : a = y * (y⁻¹ * a * y) * y⁻¹ := by group
      rw [this, h1]
      group
    have pow3 : (y⁻¹ * a * y) ^ 3 = 1 := by
      have hconjpow : ∀ m : ℕ, (y⁻¹ * a * y) ^ m = y⁻¹ * a ^ m * y := by
        intro m
        induction m with
        | zero => group
        | succ m ih => rw [pow_succ, ih, pow_succ]; group
      rw [hconjpow 3, ha3]
      group
    have hIE : IsEkIn 3 1 A (Subgroup.zpowers (y⁻¹ * a * y)) :=
      ⟨Subgroup.zpowers_le.2 hcA, CFSG.Open.isElemAbelian_zpowers pow3, by
        rw [Nat.card_zpowers, orderOf_eq_prime pow3 hne1]
        norm_num⟩
    have hG : GConj (Subgroup.zpowers a) (Subgroup.zpowers (y⁻¹ * a * y)) := ⟨y, glbConj_zpowers y a⟩
    exact ((h1112iii _ hIE).2 hG) (Subgroup.zpowers_le.2 hc)
  have hc1 : y⁻¹ * a * y ≠ 1 := by
    intro h1
    apply hcon
    rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨x_c, hx_c, k, hk, hck⟩ := coord_decomp hAel hA27 hA₀A hA0card ha ha1 haA0 hcA
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hcA0
    rw [hck, pow_zero, mul_one]
    exact hx_c
  have hxc1 : x_c ≠ 1 := by
    rintro rfl
    apply hcon
    rw [hck, one_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) k
  have hzD : ∃ z ∈ E ⊓ A, z ≠ 1 ∧ Subgroup.zpowers (z * a ^ k) = Subgroup.zpowers a₁ := by
    rcases (show k = j ∨ k + j = 3 by omega) with hkj | hkj
    · refine ⟨x₁, hx1A₀, hx11, ?_⟩
      rw [hkj, ha₁eq]
    · refine ⟨x₁⁻¹, (E ⊓ A).inv_mem hx1A₀, inv_ne_one.2 hx11, ?_⟩
      have hak : a ^ k = (a ^ j)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_add, hkj, ha3]
      have hcomm : Commute x₁ (a ^ j) := elemAb_comm hAel (hA₀A hx1A₀) (A.pow_mem ha j)
      have hinv : x₁⁻¹ * a ^ k = (x₁ * a ^ j)⁻¹ := by
        rw [hak, mul_inv_rev]
        exact (show Commute x₁ (a ^ j) from hcomm).inv_inv.eq
      rw [hinv, ← ha₁eq, Subgroup.zpowers_inv]
  obtain ⟨z, hz_mem, hz1, hzz⟩ := hzD
  obtain ⟨n, hnK, hnN, hn⟩ := hF1 x_c hx_c hxc1 z hz_mem hz1
  have hcm : n * a ^ k = a ^ k * n := ((hKa n hnK).pow_right k).eq
  have hnak : n⁻¹ * a ^ k * n = a ^ k := by
    calc n⁻¹ * a ^ k * n = n⁻¹ * (a ^ k * n) := by group
      _ = n⁻¹ * (n * a ^ k) := by rw [hcm]
      _ = a ^ k := by group
  have hnA : n ∈ Subgroup.normalizer (A : Set G) :=
    normalizes_of_commute hAel hA27 hA₀A hA0card ha ha1 haA0 (hKa n hnK) hnN
  have hyn : y * n ∈ M ⊓ Subgroup.normalizer (A : Set G) :=
    Subgroup.mem_inf.2 ⟨M.mul_mem hyM (hNM hnN), Subgroup.mul_mem _ hyN hnA⟩
  have hgen : Subgroup.zpowers (n⁻¹ * (y⁻¹ * a * y) * n) = Subgroup.zpowers a₁ := by
    rw [← hzz]
    congr 1
    rw [hck, show n⁻¹ * (x_c * a ^ k) * n = (n⁻¹ * x_c * n) * (n⁻¹ * a ^ k * n) by group, hn, hnak]
  have hPc : PzProp M A (n⁻¹ * (y⁻¹ * a * y) * n) ↔ PzProp M A a₁ := pzProp_zpowers_eq hgen
  have hPconj : PzProp M A ((y * n)⁻¹ * a * (y * n)) ↔ PzProp M A a := pz_conj (M.mul_mem hyM (hNM hnN))
    (Subgroup.mul_mem _ hyN hnA)
  have e : (y * n)⁻¹ * a * (y * n) = n⁻¹ * (y⁻¹ * a * y) * n := by group
  rw [e] at hPconj
  exact hPa1 (hPc.1 (hPconj.2 hPa))

theorem isPGroup_of_le' {p : ℕ} {T H : Subgroup G} (hT : IsPGroup p T) (hH : H ≤ T) :
    IsPGroup p H := by
  intro x
  obtain ⟨k, hk⟩ := hT ⟨(x : G), hH x.2⟩
  exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩

theorem isPGroup_pCoreOf_two (M : Subgroup G) : IsPGroup 2 (pCoreOf 2 M) := by
  intro x
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 x.2
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) ⟨y, hy⟩
  have hk' : (y : G) ^ (2 ^ k) = 1 := by
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥M) => ((z : ↥M) : G)) hk
    simpa using this
  exact ⟨k, Subtype.ext (by simpa [← hyx] using hk')⟩

theorem not_isCyclic_of_elemAb {A : Subgroup G} (hAel : IsElemAbelian 3 A) (hA27 : Nat.card A = 27) :
    ¬ IsCyclic ↥A := by
  intro hc
  haveI : IsCyclic ↥A := hc
  have h1 := IsCyclic.exponent_eq_card (α := ↥A)
  have hdvd : Monoid.exponent ↥A ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun x : ↥A => Subtype.ext (by simpa using hAel.2 (x : G) x.2))
  rw [h1, hA27] at hdvd
  norm_num at hdvd

theorem conj_sup_le {C K₁ O' : Subgroup G} (hK : ∀ g ∈ C, ∀ k ∈ K₁, g * k * g⁻¹ ∈ K₁)
    (hO : ∀ g ∈ C, ∀ o ∈ O', g * o * g⁻¹ ∈ O') {g : G} (hg : g ∈ C) {y : G}
    (hy : y ∈ K₁ ⊔ O') : g * y * g⁻¹ ∈ K₁ ⊔ O' := by
  let Hc : Subgroup G := (K₁ ⊔ O').comap (MulAut.conj g).toMonoidHom
  have hKc : K₁ ≤ Hc := fun k hk => by
    show g * k * g⁻¹ ∈ K₁ ⊔ O'
    exact Subgroup.mem_sup_left (hK g hg k hk)
  have hOc : O' ≤ Hc := fun o ho => by
    show g * o * g⁻¹ ∈ K₁ ⊔ O'
    exact Subgroup.mem_sup_right (hO g hg o ho)
  have hle : K₁ ⊔ O' ≤ Hc := sup_le hKc hOc
  exact hle hy

theorem card_gLBConj' (x : G) (S : Subgroup G) : Nat.card (GLBConj x S) = Nat.card S := by
  unfold GLBConj
  exact Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective

theorem odd_glaPPrimeCore_of_conj {a a₁ g : G} (hg : GLBConj g (Subgroup.zpowers a) = Subgroup.zpowers a₁)
    (hodd : Odd (Nat.card ↥(GLAPPrimeCoreOf 3 (Cg a)))) :
    Odd (Nat.card ↥(GLAPPrimeCoreOf 3 (Cg a₁))) := by
  have hb : Subgroup.zpowers (g⁻¹ * a * g) = Subgroup.zpowers a₁ := by
    rw [← glbConj_zpowers, hg]
  have hCb : GLBConj g (Cg a) = Cg a₁ := by
    rw [glbConj_centralizer_singleton, centralizer_singleton_eq_of_zpowers_eq hb]
  have hO : GLAPPrimeCoreOf 3 (Cg a₁) = GLBConj g (GLAPPrimeCoreOf 3 (Cg a)) := by
    rw [← hCb, glaPPrimeCoreOf_gLBConj]
  rw [hO, card_gLBConj']
  exact hodd

theorem zpowers_pow_eq_of_order_three {a : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) {j : ℕ} (hj : j < 3)
    (hj0 : j ≠ 0) : Subgroup.zpowers (a ^ j) = Subgroup.zpowers a := by
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
  · rw [pow_one]
  · apply le_antisymm
    · exact Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 2)
    · apply Subgroup.zpowers_le.2
      have h4 : (a ^ 2) ^ 2 = a := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, ha3, one_mul, pow_one]
      have := Subgroup.pow_mem _ (Subgroup.mem_zpowers (a ^ 2)) 2
      rwa [h4] at this

theorem commutator_le_of_normal {T S A : Subgroup G} (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hS : S ≤ T) : ⁅S, A⁆ ≤ T := by
  rw [Subgroup.commutator_le]
  intro s hs b hb
  have e : ⁅s, b⁆ = s * (b * s * b⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  have hbs : b * s * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hAT hb) s).1 (hS hs)
  exact T.mul_mem (hS hs) (T.inv_mem hbs)

theorem glaPPrimeCoreOf_le_self' (H : Subgroup G) : GLAPPrimeCoreOf 3 H ≤ H := by
  unfold GLAPPrimeCoreOf
  exact Subgroup.map_subtype_le _

theorem not_odd_core {m : ℕ} {B M E A K : Subgroup G} {a : G} (h : Cex117 G m 3 B M E A a K)
    (hIL : IsLThreeFour (barOf 3 K)) (hcharTwo : IsCharTwoType G) (hTwoLocM : IsTwoLocal M)
    (hAM : A ≤ M) (hAel : IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hA0card : Nat.card ((E ⊓ A : Subgroup G)) = 9)
    (ha : a ∈ A) (ha1 : a ≠ 1) (haA0 : a ∉ E ⊓ A) (hKa : ∀ n ∈ K, Commute n a)
    (hF1 : ∀ x ∈ E ⊓ A, x ≠ 1 → ∀ y ∈ E ⊓ A, y ≠ 1 →
      ∃ n ∈ K, n ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ∧ n⁻¹ * x * n = y)
    (hNM : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M)
    (h1112iii : ∀ U : Subgroup G, IsEkIn 3 1 A U → (¬ U ≤ E ⊓ A ↔ GConj (Subgroup.zpowers a) U))
    (hF2 : ∀ a₁ ∈ A, a₁ ∉ E ⊓ A → ∀ K₁ : Subgroup G, GLAPComponent 3 (Cg a₁) K₁ →
      IsLThreeFour (barOf 3 K₁) →
      ∀ S : Subgroup G, S ≤ Cg a₁ → ¬ 3 ∣ Nat.card S → A ≤ Subgroup.normalizer (S : Set G) →
        S ≤ K₁ ⊔ GLAPPrimeCoreOf 3 (Cg a₁) ⊔ Subgroup.centralizer (A : Set G))
    (hFaI : ⁅(pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G), A⁆ ≤
      GLAPPrimeCoreOf 3 (Cg a))
    (hFbI : ∀ a₁ ∈ A, a₁ ∉ E ⊓ A → ∀ K₁ : Subgroup G, GLAPComponent 3 (Cg a₁) K₁ →
      IsLThreeFour (barOf 3 K₁) →
      (∀ g ∈ Cg a₁, ∀ k ∈ K₁, g * k * g⁻¹ ∈ K₁) ∧
        pCoreOf 2 (K₁ ⊔ GLAPPrimeCoreOf 3 (Cg a₁)) ≤ GLAPPrimeCoreOf 3 (Cg a₁))
    (h111 : ∀ b ∈ A, b ≠ 1 → GLAPPrimeCoreOf 3 (Cg b) ≤ M)
    (hodd : Odd (Nat.card ↥(GLAPPrimeCoreOf 3 (Cg a)))) : False := by
  have hA1 : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hA27
    norm_num at hA27
  have hT2 : IsPGroup 2 (pCoreOf 2 M) := isPGroup_pCoreOf_two M
  have hAT : A ≤ Subgroup.normalizer ((pCoreOf 2 M : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      exact pCoreOf_two_conj_mem (hAM hx) ht
    · intro ht
      have := pCoreOf_two_conj_mem (M.inv_mem (hAM hx)) ht
      have e : x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ = t := by group
      rwa [e] at this
  obtain ⟨⟨A₁, A₂, hne, hA1le, hA2le, hi1, hi2, hc1, hc2⟩, -⟩ :=
    (GL83.I_33_1_proved G hcharTwo 3 Nat.prime_three (by norm_num) A (pCoreOf 2 M) hA1 hAel hT2 hAT
      (Or.inr (Or.inl ⟨M, hTwoLocM, hAM, rfl⟩))).2 A hA1 le_rfl (not_isCyclic_of_elemAb hAel hA27)
  obtain ⟨Ai, hAi_le, hAi_idx, hAi_comm, hAi_ne⟩ : ∃ Ai : Subgroup G, Ai ≤ A ∧
      (Ai.subgroupOf A).index = 3 ∧
        ⁅A, (pCoreOf 2 M ⊓ Subgroup.centralizer (Ai : Set G) : Subgroup G)⁆ ≠ ⊥ ∧
        Ai ≠ E ⊓ A := by
    by_cases h1 : A₁ = E ⊓ A
    · exact ⟨A₂, hA2le, hi2, hc2, fun h2 => hne (h1.trans h2.symm)⟩
    · exact ⟨A₁, hA1le, hi1, hc1, h1⟩
  have hAi_card : Nat.card Ai = 9 := by
    have := card_of_index_three_gen hAi_le hA27 hAi_idx
    omega
  obtain ⟨a₁, ha₁Ai, ha₁A₀⟩ : ∃ a₁ ∈ Ai, a₁ ∉ E ⊓ A := by
    by_contra hcon
    push Not at hcon
    exact hAi_ne (Subgroup.eq_of_le_of_card_ge (fun d hd => hcon d hd) (by omega))
  have ha₁A : a₁ ∈ A := hAi_le ha₁Ai
  have ha₁1 : a₁ ≠ 1 := by
    intro h1
    apply ha₁A₀
    rw [h1]
    exact (E ⊓ A).one_mem
  have hPa1 : ¬ PzProp M A a₁ := by
    intro hP
    apply hAi_comm
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro b hb s hs
    obtain ⟨hsT, hsC⟩ := Subgroup.mem_inf.1 hs
    have hsa : s * a₁ = a₁ * s := (Subgroup.mem_centralizer_iff.1 hsC a₁ ha₁Ai).symm
    have hcomm : s * b = b * s := hP s hsT hsa b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.symm
  have hPa : PzProp M A a := by
    obtain ⟨S, hSdef⟩ : ∃ S : Subgroup G, S = pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G) :=
      ⟨_, rfl⟩
    have hSle : S ≤ pCoreOf 2 M := hSdef ▸ inf_le_left
    have hcomm : ⁅S, A⁆ ≤ GLAPPrimeCoreOf 3 (Cg a) := by
      rw [hSdef]
      exact hFaI
    have hbot : ⁅S, A⁆ = ⊥ := by
      exact eq_bot_of_two_le_odd (isPGroup_of_le' hT2 (commutator_le_of_normal hAT hSle)) hcomm hodd
    intro t ht hta b hb
    have htS : t ∈ S := by
      rw [hSdef]
      exact Subgroup.mem_inf.2 ⟨ht, Subgroup.mem_centralizer_singleton_iff.2 hta⟩
    have hmem : ⁅b, t⁆ ∈ ⁅A, S⁆ := Subgroup.commutator_mem_commutator hb htS
    rw [Subgroup.commutator_comm, hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem.symm
  obtain ⟨x₁, hx₁A₀, j, hj, ha₁eq⟩ := coord_decomp hAel hA27 inf_le_right hA0card ha ha1 haA0 ha₁A
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply ha₁A₀
    rw [ha₁eq, pow_zero, mul_one]
    exact hx₁A₀
  have ha3 : a ^ 3 = 1 := hAel.2 a ha
  have hx₁1 : x₁ ≠ 1 := by
    intro hx
    rw [hx, one_mul] at ha₁eq
    have hz : Subgroup.zpowers a = Subgroup.zpowers a₁ := by
      rw [ha₁eq]
      exact (zpowers_pow_eq_of_order_three ha3 ha1 hj hj0).symm
    exact hPa1 ((pzProp_zpowers_eq hz).1 hPa)
  have hNa : ∀ y ∈ M ⊓ Subgroup.normalizer (A : Set G), y⁻¹ * a * y ∈ Subgroup.zpowers a :=
    fun y hy => zpowers_conj_of_pz hAel hA27 hA0card ha ha1 haA0 hKa hF1 hNM h1112iii hPa hPa1
      hx₁A₀ hx₁1 ha₁eq ha₁A ha₁A₀ hj hj0 hy
  have hNormA : NormalizesCyc M A a := by
    unfold NormalizesCyc
    intro y hy
    have h1 := hNa y hy
    have h2 := hNa y⁻¹ (Subgroup.inv_mem _ hy)
    rw [inv_inv] at h2
    exact normalizes_zpowers_of_conj h1 h2
  have hnotN := not_normalizes_a1 hAel hA27 hA0card ha ha1 haA0 hKa hF1 hNM hx₁A₀ hx₁1 ha₁eq hj hj0
  have hIE : IsEkIn 3 1 A (Subgroup.zpowers a₁) :=
    ⟨Subgroup.zpowers_le.2 ha₁A, CFSG.Open.isElemAbelian_zpowers (hAel.2 a₁ ha₁A), by
      rw [Nat.card_zpowers, orderOf_eq_prime (hAel.2 a₁ ha₁A) ha₁1]
      norm_num⟩
  have hnotle : ¬ Subgroup.zpowers a₁ ≤ E ⊓ A := fun hle => ha₁A₀ (Subgroup.zpowers_le.1 hle)
  have hGC : GConj (Subgroup.zpowers a) (Subgroup.zpowers a₁) := (h1112iii _ hIE).1 hnotle
  obtain ⟨K₁, hK₁comp, hIL₁, hK₁M⟩ := K1_le_M h hIL hNormA ha₁A ha₁A₀ hnotN hGC
  obtain ⟨hKn, hO2⟩ := hFbI a₁ ha₁A ha₁A₀ K₁ hK₁comp hIL₁
  have hOdd₁ : Odd (Nat.card ↥(GLAPPrimeCoreOf 3 (Cg a₁))) := by
    obtain ⟨g, hg⟩ := hGC
    exact odd_glaPPrimeCore_of_conj hg hodd
  have hS₁C : (pCoreOf 2 M ⊓ Subgroup.centralizer (Ai : Set G) : Subgroup G) ≤ Cg a₁ :=
    inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 ha₁Ai))
  have hS₁2 : IsPGroup 2 ↥(pCoreOf 2 M ⊓ Subgroup.centralizer (Ai : Set G) : Subgroup G) :=
    isPGroup_of_le' hT2 inf_le_left
  have hS₁card : ¬ 3 ∣ Nat.card ↥(pCoreOf 2 M ⊓ Subgroup.centralizer (Ai : Set G) : Subgroup G) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hS₁2
    intro hd
    rw [hn] at hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    norm_num at this
  have hAS₁ : A ≤ Subgroup.normalizer ((pCoreOf 2 M ⊓ Subgroup.centralizer (Ai : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_centralizer_set hAT (fun x hx s hs => elemAb_comm hAel hx (hAi_le hs))
  have hF2S := hF2 a₁ ha₁A ha₁A₀ K₁ hK₁comp hIL₁ _ hS₁C hS₁card hAS₁
  have hAC : A ≤ Cg a₁ := fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (elemAb_comm hAel hx ha₁A)
  have hKC : K₁ ≤ Cg a₁ := hK₁comp.1
  have hOC : GLAPPrimeCoreOf 3 (Cg a₁) ≤ Cg a₁ := glaPPrimeCoreOf_le_self' _
  have hCAC : Subgroup.centralizer (A : Set G) ≤ Cg a₁ :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 ha₁A)
  have hOn : ∀ g ∈ Cg a₁, ∀ o ∈ GLAPPrimeCoreOf 3 (Cg a₁), g * o * g⁻¹ ∈ GLAPPrimeCoreOf 3 (Cg a₁) :=
    fun g hg o ho => glaPPrimeCoreOf_conj_mem' hg ho
  have hYn : ∀ g ∈ Cg a₁, ∀ y ∈ K₁ ⊔ GLAPPrimeCoreOf 3 (Cg a₁),
      g * y * g⁻¹ ∈ K₁ ⊔ GLAPPrimeCoreOf 3 (Cg a₁) :=
    fun g hg y hy => conj_sup_le hKn hOn hg hy
  have hcomm1 : ⁅(pCoreOf 2 M ⊓ Subgroup.centralizer (Ai : Set G) : Subgroup G), A⁆ ≤
      K₁ ⊔ GLAPPrimeCoreOf 3 (Cg a₁) :=
    commutator_le_of_sup hAC hKC hOC hCAC hKn hOn hYn le_sup_left le_sup_right hF2S
  have hYM : K₁ ⊔ GLAPPrimeCoreOf 3 (Cg a₁) ≤ M := sup_le hK₁M (h111 a₁ ha₁A ha₁1)
  have hYC : K₁ ⊔ GLAPPrimeCoreOf 3 (Cg a₁) ≤ Cg a₁ := sup_le hKC hOC
  have hWle : pCoreOf 2 M ⊓ (K₁ ⊔ GLAPPrimeCoreOf 3 (Cg a₁)) ≤ pCoreOf 2 (K₁ ⊔ GLAPPrimeCoreOf 3 (Cg a₁)) :=
    le_pCoreOf_two_of_normal inf_le_right (isPGroup_of_le' hT2 inf_le_left)
      (fun y hy w hw => ⟨pCoreOf_two_conj_mem (hYM hy) hw.1, hYn y (hYC hy) w hw.2⟩)
  have hcomm2 : ⁅(pCoreOf 2 M ⊓ Subgroup.centralizer (Ai : Set G) : Subgroup G), A⁆ ≤
      pCoreOf 2 M ⊓ (K₁ ⊔ GLAPPrimeCoreOf 3 (Cg a₁)) :=
    le_inf (commutator_le_of_normal hAT inf_le_left) hcomm1
  have hbot : ⁅(pCoreOf 2 M ⊓ Subgroup.centralizer (Ai : Set G) : Subgroup G), A⁆ = ⊥ :=
    eq_bot_of_two_le_odd
      (isPGroup_of_le' hT2 (commutator_le_of_normal hAT inf_le_left))
      ((hcomm2.trans hWle).trans hO2) hOdd₁
  exact hAi_comm (by rw [Subgroup.commutator_comm]; exact hbot)

theorem glaPPrimeCoreOf_cg_card (a : G) :
    Nat.card ↥(GLAPPrimeCoreOf 3 (Cg a)) = Nat.card ↥(GLAPPrimeCore 3 ↥(Cg a)) := by
  unfold GLAPPrimeCoreOf
  rw [Subgroup.card_map_of_injective (Cg a).subtype_injective]

theorem map_normalizer_mem {H K : Type*} [Group H] [Group K] (f : H →* K)
    {S : Subgroup H} {w : H} (hw : w ∈ Subgroup.normalizer (S : Set H)) :
    f w ∈ Subgroup.normalizer ((S.map f : Subgroup K) : Set K) := by
  have fwd : ∀ v ∈ Subgroup.normalizer (S : Set H), ∀ x ∈ S.map f,
      f v * x * (f v)⁻¹ ∈ S.map f := by
    intro v hv x hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨v * s * v⁻¹, (Subgroup.mem_normalizer_iff.1 hv s).1 hs, ?_⟩
    simp [map_mul, map_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fwd w hw x
  · intro hx
    have h2 := fwd w⁻¹ (Subgroup.inv_mem _ hw) _ hx
    rw [map_inv] at h2
    have e : (f w)⁻¹ * (f w * x * (f w)⁻¹) * ((f w)⁻¹)⁻¹ = x := by group
    rwa [e] at h2

theorem exists_two_local_cover (a : G) {A : Subgroup G} (hAC : A ≤ Cg a)
    (hAel : IsElemAbelian 3 A) (hev : Even (Nat.card ↥(GLAPPrimeCoreOf 3 (Cg a)))) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ A ≤ Subgroup.normalizer (T : Set G) ∧
      ∀ X : Subgroup G, barX 3 (Cg a) X ≤ barX 3 (Cg a) (Subgroup.normalizer (T : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := glaPPrimeCoreOf_cg_card a
  have hNeven : Even (Nat.card ↥(GLAPPrimeCore 3 ↥(Cg a))) := by rw [← hcard]; exact hev
  have hNcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥(Cg a))) := by
    rw [← hcard]; exact sec11_glaPPrimeCoreOf_coprime (Cg a)
  have hNnorm : Subgroup.normalizer
      ((GLAPPrimeCore 3 ↥(Cg a) : Subgroup ↥(Cg a)) : Set ↥(Cg a)) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.2 inferInstance
  have hA'N : A.subgroupOf (Cg a) ≤
      Subgroup.normalizer ((GLAPPrimeCore 3 ↥(Cg a) : Subgroup ↥(Cg a)) : Set ↥(Cg a)) := by
    rw [hNnorm]; exact le_top
  letI act : MulDistribMulAction ↥(A.subgroupOf (Cg a)) ↥(GLAPPrimeCore 3 ↥(Cg a)) :=
    conjAct (A.subgroupOf (Cg a)) (GLAPPrimeCore 3 ↥(Cg a)) hA'N
  haveI : Fact (IsPGroup 3 ↥(A.subgroupOf (Cg a))) :=
    ⟨CFSG.Open.IsElemAbelian.isPGroup (CFSG.Open.IsElemAbelian.subgroupOf hAel (Cg a))⟩
  obtain ⟨P, hPinv⟩ := CFSG.exists_invariant_sylow (G := ↥(GLAPPrimeCore 3 ↥(Cg a)))
    (A := ↥(A.subgroupOf (Cg a))) (p := 3) (q := 2) hNcop
  have hPne : P.toSubgroup ≠ ⊥ := by
    intro hbot
    have hnd : ¬ 2 ∣ P.toSubgroup.index := P.not_dvd_index
    rw [hbot, Subgroup.index_bot] at hnd
    exact hnd (even_iff_two_dvd.1 hNeven)
  have hfrat := Sylow.normalizer_sup_eq_top P
  set T₁ : Subgroup ↥(Cg a) := P.toSubgroup.map (GLAPPrimeCore 3 ↥(Cg a)).subtype with hT₁def
  set T : Subgroup G := T₁.map (Cg a).subtype with hTdef
  have hT₁2 : IsPGroup 2 T₁ := P.isPGroup'.map (GLAPPrimeCore 3 ↥(Cg a)).subtype
  have hT2 : IsPGroup 2 T := hT₁2.map (Cg a).subtype
  have hT₁ne : T₁ ≠ ⊥ := by
    intro h
    apply hPne
    apply Subgroup.map_injective (f := (GLAPPrimeCore 3 ↥(Cg a)).subtype)
      (GLAPPrimeCore 3 ↥(Cg a)).subtype_injective
    rw [Subgroup.map_bot]
    exact h
  have hT_ne : T ≠ ⊥ := by
    intro h
    apply hT₁ne
    apply Subgroup.map_injective (f := (Cg a).subtype) (Cg a).subtype_injective
    rw [Subgroup.map_bot]
    exact h
  have hinv : ∀ w : ↥(Cg a), w ∈ A.subgroupOf (Cg a) → ∀ s : ↥(Cg a),
      s ∈ T₁ ↔ w * s * w⁻¹ ∈ T₁ := by
    intro w hw s
    constructor
    · intro hs
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hs
      exact Subgroup.mem_map.2 ⟨(⟨w, hw⟩ : ↥(A.subgroupOf (Cg a))) • y,
        (hPinv.invariant (⟨w, hw⟩ : ↥(A.subgroupOf (Cg a))) y).1 hy, rfl⟩
    · intro hs
      obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.1 hs
      refine Subgroup.mem_map.2 ⟨((⟨w, hw⟩ : ↥(A.subgroupOf (Cg a)))⁻¹) • z,
        (hPinv.invariant _ z).1 hz, ?_⟩
      show (w⁻¹ : ↥(Cg a)) * (GLAPPrimeCore 3 ↥(Cg a)).subtype z * (w⁻¹)⁻¹ = s
      rw [hzeq]
      group
  have hwN : ∀ w : ↥(Cg a), w ∈ A.subgroupOf (Cg a) →
      w ∈ Subgroup.normalizer (T₁ : Set ↥(Cg a)) :=
    fun w hw => Subgroup.mem_normalizer_iff.2 (hinv w hw)
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := by
    intro x hx
    exact map_normalizer_mem (Cg a).subtype (hwN ⟨x, hAC hx⟩ (Subgroup.mem_subgroupOf.2 hx))
  refine ⟨T, hT_ne, hT2, hAT, ?_⟩
  intro X q hq
  obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hq
  have hk : k ∈ Subgroup.normalizer (T₁ : Set ↥(Cg a)) ⊔ GLAPPrimeCore 3 ↥(Cg a) := by
    rw [hfrat]; exact Subgroup.mem_top k
  obtain ⟨u, hu, n, hn, hkun⟩ := Subgroup.mem_sup_of_normal_right.1 hk
  refine Subgroup.mem_map.2 ⟨u, Subgroup.mem_subgroupOf.2
    (map_normalizer_mem (Cg a).subtype hu), ?_⟩
  rw [← hkun, map_mul]
  simp [hn]

theorem _root_.CFSG.LocalAnalysis.GLTheoremB.MovingAround.lemma1115_i_of_inputs
    (h1111 : Lemma1111Statement) (h119 : Lemma119Statement) (h1112 : Lemma1112Statement)
    (h111 : Prop111Statement) (hF1 : Lemma1114FusionInput) (hF2 : Lemma1114ChiefInput)
    (hFa : Lemma1115ChiefAInput) (hFb : Lemma1115CompInput) :
    Lemma1115_iStatement := by
  intro G _ _ m p B M E A a K h
  obtain ⟨rfl, hA3, hIL⟩ := h1111 h
  have hsec : Sec11 G m 3 B M E A := h.toCex117Base.toSec11
  have hE : inD 3 M E := hsec.pair.1.1
  have hAp : inDp 3 M A := hsec.pair.1.2.1
  have hA0 : CFSG.Open.pRank 3 (E ⊓ A) = 2 := (h119 h).1
  have hAM : A ≤ M := hAp.1.1.1
  have hAel : IsElemAbelian 3 A := hAp.1.1.2.1
  have hA27 : Nat.card A = 27 := card_eq_27_of_pRank hAel hA3
  have hA0el : IsElemAbelian 3 (E ⊓ A : Subgroup G) :=
    CFSG.Open.IsElemAbelian.mono hAel inf_le_right
  have hA0card : Nat.card ((E ⊓ A : Subgroup G)) = 9 := by
    rw [card_eq_pow_of_pRank hA0el, hA0]
    norm_num
  have ha : a ∈ A := h.ha.1
  have ha1 : a ≠ 1 := h.ha.2
  have haA0 : a ∉ E ⊓ A := fun haE => h.notD ⟨E, hE, (Subgroup.mem_inf.1 haE).1⟩
  obtain ⟨-, -, h1112iii⟩ := h1112 h
  have hKa : ∀ n ∈ K, Commute n a := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.1 (h.hK.1 hn)
  have hNM : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M := by
    have hsub : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ GLBCore 3 2 E :=
      le_sSup ⟨E ⊓ A, inf_le_left, hA0.ge, rfl⟩
    exact hsub.trans hE.2.clause_d
  have hcharTwo : IsCharTwoType G := h.standing.charTwo
  have hTwoLocM : IsTwoLocal M := hE.2.maxTwoLocal.1
  have hAC : A ≤ Cg a := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (elemAb_comm hAel hx ha)
  have hnotodd : ¬ Odd (Nat.card ↥(GLAPPrimeCoreOf 3 (Cg a))) := fun hodd =>
    not_odd_core h hIL hcharTwo hTwoLocM hAM hAel hA27 hA0card ha ha1 haA0 hKa
      (hF1 h rfl hIL) hNM h1112iii (hF2 h rfl hIL) (hFa h rfl hIL) (hFb h rfl hIL)
      (fun b hb hb1 => h111 hsec hb hb1) hodd
  have hev : Even (Nat.card ↥(GLAPPrimeCoreOf 3 (Cg a))) :=
    (Nat.even_or_odd _).resolve_right hnotodd
  obtain ⟨T, hTne, hT2, hAT, hcov⟩ := exists_two_local_cover a hAC hAel hev
  exact ⟨Subgroup.normalizer (T : Set G), ⟨T, hTne, hT2, rfl⟩, hAT, hcov K⟩

end Lemma1114
