module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_9
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem glaPPrimeCoreOf_eq_self_of_coprime {G : Type*} [Group G] {p : ℕ} {H : Subgroup G}
    (h : Nat.Coprime p (Nat.card H)) : GLAPPrimeCoreOf p H = H := by
  have hN : (⊤ : Subgroup ↥H) ≤ GLAPPrimeCore p ↥H :=
    le_sSup ⟨inferInstance, by
      rw [Nat.card_congr (Subgroup.topEquiv (G := ↥H)).toEquiv]; exact h⟩
  have htop : GLAPPrimeCore p ↥H = ⊤ := top_unique hN
  unfold GLAPPrimeCoreOf
  rw [htop, Subgroup.map_top, Subgroup.range_subtype]

theorem glaPPrimeCoreOf_top_eq_bot_of_eq_bot {Q : Type*} [Group Q] {p : ℕ}
    (h : GLAPPrimeCore p Q = ⊥) : GLAPPrimeCoreOf p (⊤ : Subgroup Q) = ⊥ := by
  have h1 := glaPPrimeCore_map_iso p (Subgroup.topEquiv (G := Q))
  rw [h] at h1
  have hsub : (⊤ : Subgroup Q).subtype = (Subgroup.topEquiv (G := Q)).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  unfold GLAPPrimeCoreOf
  rw [hsub, h1]

theorem not_barX_le_centralizer_of_isSCp {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) {B L : Subgroup X} (hB : IsSCp p ⊤ B)
    (hL : GLAPComponent p ⊤ L) :
    ¬ barX p ⊤ B ≤ Subgroup.centralizer
      (barX p ⊤ L : Set (↥(⊤ : Subgroup X) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup X))) := by
  have : Fact p.Prime := ⟨hp⟩
  set Z : Type _ := ↥(⊤ : Subgroup X) with hZ
  set N : Subgroup Z := GLAPPrimeCore p Z with hNdef
  have hNcop : Nat.Coprime p (Nat.card N) := CFSG.pPrimeCore_coprime_card
  have hN : ¬ p ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd hp).1 hNcop
  have hB1 : IsSCp p ⊤ (B.subgroupOf (⊤ : Subgroup X)) := isSCp_subgroupOf hB le_top
  have hB2 : IsSCp p ⊤ (barX p ⊤ B) := isSCp_map_quotient N hN hB1
  have hLc : IsComponentOf (barX p ⊤ L) ⊤ := hL.2.2.1
  have hcore : GLAPPrimeCore p (Z ⧸ N) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hLq := hLc.2.2
  have hpdvd : p ∣ Nat.card (barX p ⊤ L) := by
    by_contra hndvd
    have hcop : Nat.Coprime p (Nat.card (barX p ⊤ L)) := (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd
    have h1 : barX p ⊤ L ≤ GLAPPrimeCoreOf p (⊤ : Subgroup (Z ⧸ N)) := by
      rw [← glaPPrimeCoreOf_eq_self_of_coprime hcop]
      exact glaPPrimeCoreOf_le_of_isSubnormal hp hLc.2.1
    rw [glaPPrimeCoreOf_top_eq_bot_of_eq_bot hcore, le_bot_iff] at h1
    have hnt : Nontrivial (barX p ⊤ L) := CFSG.ComponentClassification.Quasisimple.nontrivial hLq
    exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt h1
  obtain ⟨x, hxord, hxc⟩ := exists_orderOf_eq_prime_not_mem_center hLq hp hodd hpdvd
  intro hc
  have hxcent : (x : Z ⧸ N) ∈ Subgroup.centralizer ((barX p ⊤ B : Subgroup (Z ⧸ N)) : Set (Z ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.1 (hc hb) x x.2).symm
  have hxB : (x : Z ⧸ N) ∈ barX p ⊤ B :=
    mem_of_mem_centralizer_orderOf_eq_prime hB2 hxcent (by rw [Subgroup.orderOf_coe]; exact hxord)
  apply hxc
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.1 (hc hxB) y y.2)

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
