module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFKindDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G] {L : Subgroup G}

section Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def ff6mPhi {hQ : Q.Nondegenerate}
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) : ↥L →* ↥(omegaProj hQ) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))

theorem ff6mPhi_apply {hQ : Q.Nondegenerate} (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (l : ↥L) : ff6mPhi e l = e (QuotientGroup.mk l) :=
  rfl

theorem ff6mPhi_surjective {hQ : Q.Nondegenerate} (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) :
    Function.Surjective (ff6mPhi e) := by
  intro w
  obtain ⟨q, hq⟩ := e.surjective w
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective q
  exact ⟨l, by rw [ff6mPhi_apply, hl, hq]⟩

theorem ff6mPhi_ker {hQ : Q.Nondegenerate} (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) :
    (ff6mPhi e).ker = Subgroup.center ↥L := by
  ext x
  rw [MonoidHom.mem_ker, ff6mPhi_apply, ← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]

theorem oddCentralCover_comp {A B P : Type} [Group A] [Group B] [Group P]
    {ρ : A →* P} (hρ : OddCentralCover ρ) (f : B ≃* A) :
    OddCentralCover (ρ.comp f.toMonoidHom) where
  surjective := by
    intro p
    obtain ⟨a, ha⟩ := hρ.surjective p
    exact ⟨f.symm a, by simp [ha]⟩
  ker_le_center := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn
    have hnc : f n ∈ Subgroup.center A := hρ.ker_le_center (by rwa [MonoidHom.mem_ker])
    rw [Subgroup.mem_center_iff] at hnc ⊢
    intro b
    apply f.injective
    rw [map_mul, map_mul, hnc]
  odd_card_ker := by
    have hker : (ρ.comp f.toMonoidHom).ker = Subgroup.comap f.toMonoidHom ρ.ker := rfl
    have hcard : Nat.card (Subgroup.comap f.toMonoidHom ρ.ker) = Nat.card ρ.ker := by
      have hmap : (Subgroup.comap f.toMonoidHom ρ.ker).map f.toMonoidHom = ρ.ker :=
        Subgroup.map_comap_eq_self_of_surjective f.surjective ρ.ker
      calc Nat.card (Subgroup.comap f.toMonoidHom ρ.ker)
          = Nat.card ((Subgroup.comap f.toMonoidHom ρ.ker).map f.toMonoidHom) :=
            (Subgroup.card_map_of_injective (f := f.toMonoidHom) f.injective).symm
        _ = Nat.card ρ.ker := by rw [hmap]
    rw [hker, hcard]
    exact hρ.odd_card_ker

theorem mulAut_eq_of_map_eq_of_perfect {A P : Type} [Group A] [Group P] {ρ : A →* P}
    (hker : ρ.ker ≤ Subgroup.center A) (hperf : commutator A = ⊤)
    {σ τ : MulAut A} (h : ∀ y : A, ρ (σ y) = ρ (τ y)) : σ = τ := by
  have hcent : ∀ y : A, σ y * (τ y)⁻¹ ∈ Subgroup.center A := fun y =>
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, h y, mul_inv_cancel])
  let n : A →* A :=
    { toFun := fun y => σ y * (τ y)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have hc : (σ b * (τ b)⁻¹) * (τ a)⁻¹ = (τ a)⁻¹ * (σ b * (τ b)⁻¹) :=
          (Subgroup.mem_center_iff.mp (hcent b) ((τ a)⁻¹)).symm
        show σ (a * b) * (τ (a * b))⁻¹ = (σ a * (τ a)⁻¹) * (σ b * (τ b)⁻¹)
        rw [map_mul, map_mul, mul_inv_rev]
        calc σ a * σ b * ((τ b)⁻¹ * (τ a)⁻¹)
            = σ a * (σ b * (τ b)⁻¹) * (τ a)⁻¹ := by group
          _ = σ a * ((σ b * (τ b)⁻¹) * (τ a)⁻¹) := by group
          _ = σ a * ((τ a)⁻¹ * (σ b * (τ b)⁻¹)) := by rw [hc]
          _ = (σ a * (τ a)⁻¹) * (σ b * (τ b)⁻¹) := by group }
  have hnker : commutator A ≤ n.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp (hcent a) (n b)).symm
  ext y
  have hy : y ∈ n.ker := hnker (by rw [hperf]; exact Subgroup.mem_top y)
  have hny : n y = 1 := MonoidHom.mem_ker.mp hy
  change σ y * (τ y)⁻¹ = 1 at hny
  rw [mul_inv_eq_one] at hny
  exact hny

theorem exists_conjAut_eq_of_cover {A P : Type} [Group A] [Group P] {ρ : A →* P}
    (hρ : OddCentralCover ρ) {σ : MulAut A} (hσ : σ * σ = 1) {α : MulAut P}
    (hαρ : ∀ y : A, ρ (σ y) = α (ρ y)) (hα2 : α * α = 1) {u : A} (hu2 : u * u = 1)
    (huσ : σ u = u) (ha : ∃ a : P, α a * a⁻¹ = ρ u) : ∃ b : A, b⁻¹ * σ b = u := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hρ.surjective ((α a)⁻¹)
  obtain ⟨t, htdef⟩ : ∃ t : A, t = b⁻¹ * σ b := ⟨_, rfl⟩
  have hρt : ρ t = ρ u := by
    rw [htdef, map_mul, map_inv, hαρ, hb]
    rw [show α ((α a)⁻¹) = a⁻¹ from by rw [map_inv, aut_apply_apply hα2 a], inv_inv]
    exact ha
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  obtain ⟨n, hndef⟩ : ∃ n : A, n = u⁻¹ * t := ⟨_, rfl⟩
  have hn : n ∈ ρ.ker := by
    rw [hndef, MonoidHom.mem_ker, map_mul, map_inv, hρt, inv_mul_cancel]
  have hnc : n ∈ Subgroup.center A := hρ.ker_le_center hn
  have hσt : σ t = t⁻¹ := by
    rw [htdef, map_mul, map_inv, aut_apply_apply hσ, mul_inv_rev, inv_inv]
  have htn : t = u * n := by rw [hndef, hu_inv, ← mul_assoc, hu2, one_mul]
  have hut : u * t = t * u := by
    have hc := Subgroup.mem_center_iff.mp hnc u
    calc u * t = u * (u * n) := by rw [← htn]
      _ = u * (n * u) := by rw [hc]
      _ = (u * n) * u := by rw [mul_assoc]
      _ = t * u := by rw [← htn]
  have hσn : σ n = n⁻¹ := by
    have h1 : σ n = u * t⁻¹ := by rw [hndef, map_mul, map_inv, huσ, hσt, hu_inv]
    have h2 : n⁻¹ = t⁻¹ * u := by rw [hndef, mul_inv_rev, inv_inv]
    rw [h1, h2]
    calc u * t⁻¹ = t⁻¹ * (t * u) * t⁻¹ := by group
      _ = t⁻¹ * (u * t) * t⁻¹ := by rw [hut]
      _ = t⁻¹ * u := by group
  obtain ⟨k, hk⟩ := hρ.exists_sqrt hn
  obtain ⟨m, hmdef⟩ : ∃ m : A, m = n ^ k := ⟨_, rfl⟩
  have hmk : m ∈ ρ.ker := by rw [hmdef]; exact Subgroup.pow_mem _ hn k
  have hmc : m ∈ Subgroup.center A := hρ.ker_le_center hmk
  have hσm : σ m = m⁻¹ := by rw [hmdef, map_pow, hσn, inv_pow]
  have hmm : m * m = n := by rw [hmdef]; exact hk
  refine ⟨b * m, ?_⟩
  have hcomm : ∀ z : A, m * z = z * m :=
    fun z => (Subgroup.mem_center_iff.mp hmc z).symm
  have hmi : m⁻¹ * t = t * m⁻¹ := by
    calc m⁻¹ * t = m⁻¹ * (t * m) * m⁻¹ := by group
      _ = m⁻¹ * (m * t) * m⁻¹ := by rw [← hcomm t]
      _ = t * m⁻¹ := by group
  calc (b * m)⁻¹ * σ (b * m) = m⁻¹ * (b⁻¹ * σ b) * σ m := by rw [map_mul]; group
    _ = m⁻¹ * t * m⁻¹ := by rw [← htdef, hσm]
    _ = t * (m * m)⁻¹ := by rw [hmi]; group
    _ = t * n⁻¹ := by rw [hmm]
    _ = u := by rw [htn]; group

theorem ff6m_phi_cover {hQ : Q.Nondegenerate} (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) : OddCentralCover (ff6mPhi e) := by
  refine ⟨ff6mPhi_surjective e, ?_, ?_⟩
  · rw [ff6mPhi_ker]
  · rw [ff6mPhi_ker]; exact hodd

theorem ff6m_phi_conj (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (l l' : ↥L)
    (hl : (l' : G) = s * l * s⁻¹) :
    ffSimOmegaAct hQ h2 x (ff6mPhi e l) = ff6mPhi e l' := by
  apply Subtype.ext
  rw [coe_ffSimOmegaAct, ff6mPhi_apply, ff6mPhi_apply]
  exact (hs.2 l l' hl).symm

theorem ff6m_exists_centCover [Finite G] (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) :
    ∃ ρ : ↥(L ⊓ centralizer ({s} : Set G)) →* ↥(ffFix hQ h2 x), OddCentralCover ρ ∧
      ∀ c : ↥(L ⊓ centralizer ({s} : Set G)),
        ((ρ c : ↥(ffFix hQ h2 x)) : ↥(omegaProj hQ)) =
          ff6mPhi e ⟨(c : G), (Subgroup.mem_inf.mp c.2).1⟩ := by
  let σ : MulAut ↥L := conjAut L hss hs.1
  let α : MulAut ↥(omegaProj hQ) := ffSimOmegaAct hQ h2 x
  have hσ2 : σ * σ = 1 := conjAut_mul_self L hss hs.1
  have hαρ : ∀ y : ↥L, ff6mPhi e (σ y) = α (ff6mPhi e y) := fun y =>
    (ff6m_phi_conj hQ h2 e hs y (σ y) (by rw [coe_conjAut])).symm
  have hρfix : OddCentralCover (fixHom (ff6mPhi e) σ α hαρ) :=
    (ff6m_phi_cover e hodd).oddCentralCover_fixHom hσ2 hαρ
  let f : ↥(L ⊓ centralizer ({s} : Set G)) ≃* ↥(fixSub σ) :=
    (fixConjEquiv L hss hs.1).symm
  refine ⟨(fixHom (ff6mPhi e) σ α hαρ).comp f.toMonoidHom, oddCentralCover_comp hρfix f, ?_⟩
  intro c
  show ((fixHom (ff6mPhi e) σ α hαρ) (f c) : ↥(omegaProj hQ)) = ff6mPhi e ⟨(c : G), _⟩
  rw [coe_fixHom]
  congr 1

theorem ff6m_cover_iff (hQ : Q.Nondegenerate) (h5 : 5 ≤ Module.finrank (ZMod 3) V)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) {u : G} (hu : u ∈ L)
    (huc : s * u = u * s) (hu2 : u * u = 1) :
    s * u ∈ conjClassIn L s ↔
      ∃ a : ↥(omegaProj hQ),
        ffSimOmegaAct hQ (by omega) x a * a⁻¹ = ff6mPhi e ⟨u, hu⟩ := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  constructor
  · rintro ⟨h, hh, hsu⟩
    refine ⟨ff6mPhi e ⟨h, hh⟩, ?_⟩
    have hsh : s * h * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hs.1 h).mp hh
    rw [ff6m_phi_conj hQ h2 e hs ⟨h, hh⟩ ⟨_, hsh⟩ rfl, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    show s * h * s⁻¹ * h⁻¹ = u
    calc s * h * s⁻¹ * h⁻¹ = s⁻¹ * (h * s * h⁻¹) := by rw [hs1]; group
      _ = s⁻¹ * (s * u) := by rw [hsu]
      _ = u := by group
  · rintro ⟨a, ha⟩
    have hα2 : ffSimOmegaAct hQ h2 x * ffSimOmegaAct hQ h2 x = 1 := by
      apply MulEquiv.ext
      intro w
      obtain ⟨y, rfl⟩ := ff6mPhi_surjective e w
      have hσ2' : conjAut L hss hs.1 * conjAut L hss hs.1 = 1 :=
        conjAut_mul_self L hss hs.1
      have k1 : ffSimOmegaAct hQ h2 x (ff6mPhi e y) = ff6mPhi e (conjAut L hss hs.1 y) :=
        ff6m_phi_conj hQ h2 e hs y (conjAut L hss hs.1 y) (by rw [coe_conjAut])
      have k2 : ffSimOmegaAct hQ h2 x (ff6mPhi e (conjAut L hss hs.1 y)) =
          ff6mPhi e (conjAut L hss hs.1 (conjAut L hss hs.1 y)) :=
        ff6m_phi_conj hQ h2 e hs (conjAut L hss hs.1 y) _ (by rw [coe_conjAut])
      rw [MulAut.mul_apply, k1, k2, aut_apply_apply hσ2', MulAut.one_apply]
    have hσ2 : conjAut L hss hs.1 * conjAut L hss hs.1 = 1 := conjAut_mul_self L hss hs.1
    have hαρ : ∀ y : ↥L, ff6mPhi e (conjAut L hss hs.1 y) =
        ffSimOmegaAct hQ h2 x (ff6mPhi e y) := fun y =>
      (ff6m_phi_conj hQ h2 e hs y _ (by rw [coe_conjAut])).symm
    have huσ : conjAut L hss hs.1 ⟨u, hu⟩ = ⟨u, hu⟩ := by
      apply Subtype.ext
      rw [coe_conjAut]
      show s * u * s⁻¹ = u
      rw [huc]; group
    have hu2' : (⟨u, hu⟩ : ↥L) * ⟨u, hu⟩ = 1 := Subtype.ext hu2
    obtain ⟨b, hb⟩ :=
      exists_conjAut_eq_of_cover (ff6m_phi_cover e hodd) hσ2 hαρ hα2 hu2' huσ ⟨a, ha⟩
    refine ⟨((b⁻¹ : ↥L) : G), L.inv_mem b.2, ?_⟩
    have hbG : ((b⁻¹ : ↥L) : G) * s * (((b⁻¹ : ↥L) : G))⁻¹ = s * u := by
      have h := congrArg Subtype.val hb
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAut] at h
      rw [Subgroup.coe_inv, inv_inv]
      calc (↑b)⁻¹ * s * ↑b
          = ((↑b)⁻¹ * (s * ↑b * s⁻¹)) * s := by group
        _ = u * s := by rw [h]
        _ = s * u := huc.symm
    exact hbG.symm

end Model

end CFSG.OddStandard.SmallF3.Omega
