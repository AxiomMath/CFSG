module

public import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

structure ExcClubHyp (G : Type) [Group G] [Finite G] (p : ℕ)
    (Exc Club : Subgroup G → Prop) : Prop where
  exc_congr : ∀ K K' : Subgroup G, Nonempty (PQuot p K ≃* PQuot p K') → (Exc K ↔ Exc K')
  club_congr : ∀ K K' : Subgroup G, Nonempty (PQuot p K ≃* PQuot p K') → (Club K ↔ Club K')
  not_club_of_exc : ∀ K : Subgroup G, Exc K → ¬ Club K
  card_center_of_exc : ∀ K : Subgroup G, Exc K → Nat.card (Subgroup.center (PQuot p K)) = p
  exc_of_not_le : ∀ (B : Subgroup G) (y : G) (K : Subgroup G), GLAIsBmax p B →
    IsEssential p B y → GLAPComponent p (Subgroup.centralizer ({y} : Set G)) K →
    ¬ B ≤ Subgroup.normalizer (K : Set G) → Exc K
  club_down : ∀ (X K : Subgroup G) (y : G), GLAPComponent p X K →
    y ^ p = 1 → y ∈ Subgroup.normalizer (K : Set G) →
    ∀ J : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J →
      Club K → Club J
  club_diag : ∀ (B : Subgroup G) (y : G) (K : Subgroup G) (b : G), GLAIsBmax p B →
    IsEssential p B y → GLAPComponent p (Subgroup.centralizer ({y} : Set G)) K → b ∈ B →
    b ∉ Subgroup.normalizer (K : Set G) →
    ∀ J : Subgroup G, GLAPComponent p (closureIn K B ⊓ Subgroup.centralizer ({b} : Set G)) J →
      Club J

@[expose] def IsGoodComp (p : ℕ) (Club : Subgroup G → Prop) (B : Subgroup G) (x : G)
    (K : Subgroup G) : Prop :=
  GLAPComponent p (Subgroup.centralizer ({x} : Set G)) K ∧
    B ≤ Subgroup.normalizer (K : Set G) ∧ ¬ Club K

@[expose] def MxB (p : ℕ) (Club : Subgroup G → Prop) (B : Subgroup G) (x : G) : Subgroup G :=
  sSup {K | IsGoodComp p Club B x K}

@[expose] noncomputable def mxB (p : ℕ) (Club : Subgroup G → Prop) (B : Subgroup G) (x : G) : ℕ :=
  Nat.card (PQuot p (MxB p Club B x))

theorem le_MxB {p : ℕ} {Club : Subgroup G → Prop} {B K : Subgroup G} {x : G}
    (hK : IsGoodComp p Club B x K) : K ≤ MxB p Club B x :=
  le_sSup hK

theorem card_pQuot_le_of_cover {p : ℕ} (hp : p.Prime) {H M M' : Subgroup G} (hHM : H ≤ M)
    (hsup : H ⊔ GLAPPrimeCoreOf p M = M) (hHM' : H ≤ M') :
    Nat.card (PQuot p M) ≤ Nat.card (PQuot p M') := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, ⟨e⟩⟩ := cover_facts hp hHM hsup
  rw [← Nat.card_congr e.toEquiv]
  set ψ : ↥H →* PQuot p M' :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥M')).comp (Subgroup.inclusion hHM') with hψ
  have hcop : Nat.Coprime p (Nat.card ψ.ker) := by
    have hle : ψ.ker.map (Subgroup.inclusion hHM') ≤ GLAPPrimeCore p ↥M' := by
      rintro _ ⟨y, hy, rfl⟩
      have : ψ y = 1 := hy
      rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    have hcard : Nat.card (ψ.ker.map (Subgroup.inclusion hHM')) = Nat.card ψ.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hHM')
    rw [← hcard]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      CFSG.pPrimeCore_coprime_card
  have hker : ψ.ker ≤ GLAPPrimeCore p ↥H := le_sSup ⟨inferInstance, hcop⟩
  have h1 : Nat.card (PQuot p H) ≤ Nat.card (↥H ⧸ ψ.ker) := by
    have hd := Subgroup.index_dvd_of_le hker
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hd
  have h2 : Nat.card (↥H ⧸ ψ.ker) = Nat.card ψ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  have h3 : Nat.card ψ.range ≤ Nat.card (PQuot p M') := Subgroup.card_le_card_group _
  omega

end CFSG.LocalAnalysis.GLTheoremA
