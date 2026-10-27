module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Components

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance.Alt

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def thetaHom (p : ℕ) {X L : Subgroup G} (hLX : L ≤ X) :
    ↥L →* ↥X ⧸ GLAPPrimeCore p ↥X :=
  (QuotientGroup.mk' (GLAPPrimeCore p ↥X)).comp (Subgroup.inclusion hLX)

theorem mem_ker_thetaHom (p : ℕ) {X L : Subgroup G} (hLX : L ≤ X) (ℓ : ↥L) :
    ℓ ∈ (thetaHom p hLX).ker ↔ Subgroup.inclusion hLX ℓ ∈ GLAPPrimeCore p ↥X := by
  rw [MonoidHom.mem_ker, thetaHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]

theorem ker_thetaHom (p : ℕ) {X L : Subgroup G} (hLX : L ≤ X) (hsn : IsSubnormal L X) :
    (thetaHom p hLX).ker = GLAPPrimeCore p ↥L := by
  refine le_antisymm ?_ ?_
  ·
    set N : Subgroup ↥L := (GLAPPrimeCore p ↥X).comap (Subgroup.inclusion hLX) with hN
    have hker : (thetaHom p hLX).ker = N := by
      ext ℓ
      rw [mem_ker_thetaHom, hN, Subgroup.mem_comap]
    rw [hker]
    have hnorm : N.Normal := Subgroup.normal_comap _
    have hcop : Nat.Coprime p (Nat.card N) := by
      have hinj : Function.Injective (Subgroup.inclusion hLX) := Subgroup.inclusion_injective hLX
      have hle : N.map (Subgroup.inclusion hLX) ≤ GLAPPrimeCore p ↥X := by
        rintro _ ⟨ℓ, hℓ, rfl⟩
        exact hℓ
      have hd : Nat.card N ∣ Nat.card (GLAPPrimeCore p ↥X) := by
        rw [← Subgroup.card_map_of_injective hinj]
        exact Subgroup.card_dvd_of_le hle
      exact (coprime_card_gLAPPrimeCore_aux p ↥X).coprime_dvd_right hd
    exact le_sSup ⟨hnorm, hcop⟩
  · intro ℓ hℓ
    rw [mem_ker_thetaHom]
    have h1 : (ℓ : G) ∈ GLAPPrimeCoreOf p L := ⟨ℓ, hℓ, rfl⟩
    obtain ⟨x, hx, hxℓ⟩ := glaPPrimeCoreOf_le_of_isSubnormal p hsn h1
    have : x = Subgroup.inclusion hLX ℓ := Subtype.ext hxℓ
    rwa [this] at hx

@[expose] noncomputable def barTheta (p : ℕ) {X L : Subgroup G} (hLX : L ≤ X)
    (hsn : IsSubnormal L X) : barOf p L →* ↥X ⧸ GLAPPrimeCore p ↥X :=
  QuotientGroup.lift (GLAPPrimeCore p ↥L) (thetaHom p hLX) (by rw [ker_thetaHom p hLX hsn])

theorem barTheta_mk (p : ℕ) {X L : Subgroup G} (hLX : L ≤ X) (hsn : IsSubnormal L X) (ℓ : ↥L) :
    barTheta p hLX hsn (QuotientGroup.mk ℓ) = QuotientGroup.mk (Subgroup.inclusion hLX ℓ) := rfl

theorem barTheta_injective (p : ℕ) {X L : Subgroup G} (hLX : L ≤ X) (hsn : IsSubnormal L X) :
    Function.Injective (barTheta p hLX hsn) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective x
  have h : ℓ ∈ (thetaHom p hLX).ker := by
    rw [MonoidHom.mem_ker]
    exact hx
  rw [ker_thetaHom p hLX hsn] at h
  exact (QuotientGroup.eq_one_iff ℓ).2 h

theorem barTheta_range (p : ℕ) {X L : Subgroup G} (hLX : L ≤ X) (hsn : IsSubnormal L X) :
    (barTheta p hLX hsn).range = barX p X L := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨Subgroup.inclusion hLX ℓ, (Subgroup.mem_subgroupOf).2 ℓ.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨QuotientGroup.mk ⟨(x : G), (Subgroup.mem_subgroupOf).1 hx⟩, rfl⟩

theorem isPerfect_barOf {p : ℕ} {X L : Subgroup G} (hL : GLAPComponent p X L) :
    Group.IsPerfect (barOf p L) := by
  have hq : Group.IsPerfect ↥(barX p X L) := ⟨hL.2.2.1.2.2.1⟩
  let e : barOf p L ≃* ↥(barX p X L) :=
    (MonoidHom.ofInjective (barTheta_injective p hL.1 hL.2.1)).trans
      (MulEquiv.subgroupCongr (barTheta_range p hL.1 hL.2.1))
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem gLAPPrimeCore_barOf (p : ℕ) (hp : p.Prime) (L : Subgroup G) :
    GLAPPrimeCore p (barOf p L) = ⊥ := by
  have := Fact.mk hp
  exact CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p

theorem odd_card_center_barOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (L : Subgroup G) :
    Odd (Nat.card (Subgroup.center (barOf p L))) := by
  have := Fact.mk hp
  have hle : Subgroup.center (barOf p L) ≤ CFSG.pCore p (barOf p L) := fun z hz =>
    mem_pCore_of_forall_comm_aux hp fun w => (Subgroup.mem_center_iff.1 hz w)
  have hpg : IsPGroup p (Subgroup.center (barOf p L)) := (CFSG.pCore_isPGroup).to_le hle
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  rw [hk]
  exact (hp.odd_of_ne_two hp2).pow

end CFSG.HardMathSupport.Timmesfeld.Balance.Alt
