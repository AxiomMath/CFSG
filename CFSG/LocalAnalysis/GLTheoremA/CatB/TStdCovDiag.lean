module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.StdCovRed
public import CFSG.LocalAnalysis.GLTheoremA.CatB.StdSmallDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def StdCovDiagCentreAt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L K B : Subgroup X) (d : X),
    CFSG.Open.IsQuasisimple ↥L → IsChevSimple 2 (PSimple 3 L) →
    IsElemAbelian 3 B → 3 ^ 4 ≤ Nat.card ↥B → InnerDiagMarking B L →
    Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) = 3 →
    d ∈ B → d ∉ Subgroup.centralizer (L : Set X) →
    CFSG.Open.IsComponentOf K (L ⊓ Subgroup.centralizer ({d} : Set X)) → SmallType 3 K →
    ∀ z ∈ K, (∀ k ∈ K, k * z = z * k) → ∀ l ∈ L, l * z = z * l

@[expose] def StdCovDiagOddAt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L K B : Subgroup X) (d : X),
    CFSG.Open.IsQuasisimple ↥L → IsChevSimple 2 (PSimple 3 L) →
    IsElemAbelian 3 B → 3 ^ 4 ≤ Nat.card ↥B → InnerDiagMarking B L →
    Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) = 3 →
    d ∈ B → d ∉ Subgroup.centralizer (L : Set X) →
    CFSG.Open.IsComponentOf K (L ⊓ Subgroup.centralizer ({d} : Set X)) → SmallType 3 K →
    Nat.Coprime 3 (Nat.card ↥(Subgroup.center ↥K))

@[expose] def StdCovDiagExclAt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L K B : Subgroup X) (d : X),
    CFSG.Open.IsQuasisimple ↥L →
    catalogIs (PSimple 3 L) (fun i => S9.isF4two i ∨ S9.isU6two i ∨ S9.isTE6two i) →
    IsElemAbelian 3 B → 3 ^ 4 ≤ Nat.card ↥B → InnerDiagMarking B L →
    Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) = 3 →
    d ∈ B → d ∉ Subgroup.centralizer (L : Set X) →
    CFSG.Open.IsComponentOf K (L ⊓ Subgroup.centralizer ({d} : Set X)) → SmallType 3 K →
    Subgroup.center ↥K = ⊥

theorem stdSubCoverAt_of_diag_facts (G : Type) [Group G] [Finite G]
    (hS : StdCovSchurAt) (hL : StdCovListAt) (hC : StdCovDiagCentreAt)
    (hO : StdCovDiagOddAt) (hE : StdCovDiagExclAt) : StdSubCoverAt G := by
  unfold StdSubCoverAt
  intro B x L D K hS' hB3 hqs hchev hidm hK hsmall hZ
  have hess := IsSStarMax.essential hS'
  have hxB : x ∈ B := hess.1
  have hx1 : x ≠ 1 := hess.2.1
  have hBel : IsElemAbelian 3 B := (IsSStarMax.bmax hS').1
  have hxp : x ^ 3 = 1 := hBel.2 x hxB
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := (IsSStarMax.component hS').1
  have hLxc : ∀ l ∈ L, l * x = x * l := fun l hl => Subgroup.mem_centralizer_singleton_iff.1 (hLx hl)
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.2 (fun l hl => hLxc l hl)
  obtain ⟨hDB, hDel, hDcard, hxD, -, hKcomp, -⟩ := hK
  have hCB : ∀ c ∈ B, c ∈ Subgroup.centralizer (L : Set G) → c ∈ Subgroup.zpowers x := by
    intro c hc hcC
    have hc3 : c ^ 3 = 1 := hBel.2 c hc
    have hcx : c * x = x * c :=
      congrArg Subtype.val (hBel.1.is_comm.comm (⟨c, hc⟩ : ↥B) ⟨x, hxB⟩)
    exact three_complement hS' hcC hc3 hcx
  have hcardC : Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) = 3 := by
    have heq : B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
      apply le_antisymm
      · intro c hc
        exact hCB c hc.1 hc.2
      · exact le_inf (Subgroup.zpowers_le.2 hxB) (Subgroup.zpowers_le.2 hxC)
    rw [heq, Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  obtain ⟨d, hdD, hdx⟩ : ∃ d ∈ D, d ∉ Subgroup.zpowers x := by
    by_contra hcon
    have hle : D ≤ Subgroup.zpowers x := fun y hy => by
      by_contra hy'
      exact hcon ⟨y, hy, hy'⟩
    have hc := Subgroup.card_le_of_le hle
    rw [hDcard, Nat.card_zpowers, orderOf_eq_prime hxp hx1] at hc
    norm_num at hc
  have hd3 : d ^ 3 = 1 := hDel.2 d hdD
  have hd1 : d ≠ 1 := fun h => hdx (h ▸ Subgroup.one_mem _)
  have hdB : d ∈ B := hDB hdD
  have hdx' : d * x = x * d :=
    congrArg Subtype.val (hDel.1.is_comm.comm (⟨d, hdD⟩ : ↥D) ⟨x, hxD⟩)
  have hdL : d ∉ Subgroup.centralizer (L : Set G) := fun hdC => hdx (hCB d hdB hdC)
  have hxnd : x ∉ Subgroup.zpowers d := by
    intro hxd
    apply hdx
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers d := Subgroup.zpowers_le.2 hxd
    have hcard : Nat.card ↥(Subgroup.zpowers d) ≤ Nat.card ↥(Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hxp hx1, orderOf_eq_prime hd3 hd1]
    have heq : Subgroup.zpowers x = Subgroup.zpowers d := Subgroup.eq_of_le_of_card_ge hle hcard
    rw [heq]
    exact Subgroup.mem_zpowers d
  have hcardsup : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers d) =
      3 * Nat.card ↥(Subgroup.zpowers d) :=
    card_sup_zpowers_of_not_mem hxp hx1 (A := Subgroup.zpowers d) (M := Subgroup.zpowers d) le_rfl hxnd
      (fun a ha => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        exact (Commute.zpow_left (show Commute d x from hdx') k).eq)
  have hzd : Nat.card ↥(Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hsupD : Subgroup.zpowers x ⊔ Subgroup.zpowers d = D := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact sup_le (Subgroup.zpowers_le.2 hxD) (Subgroup.zpowers_le.2 hdD)
    · rw [hcardsup, hzd, hDcard]
      norm_num
  have hCeq : L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({d} : Set G) := by
    ext l
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hlL, hlD⟩
      refine ⟨hlL, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.1 hlD) d hdD).symm
    · rintro ⟨hlL, hld⟩
      refine ⟨hlL, ?_⟩
      have hle : D ≤ Subgroup.centralizer ({l} : Set G) := by
        rw [← hsupD]
        refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.1 (hLx hlL)).symm
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.1 hld).symm
      exact Subgroup.mem_centralizer_iff.2 (fun h hh => Subgroup.mem_centralizer_singleton_iff.1 (hle hh))
  have hK' : CFSG.Open.IsComponentOf K (L ⊓ Subgroup.centralizer ({d} : Set G)) := by
    rw [← hCeq]
    exact hKcomp
  have hKq : CFSG.Open.IsQuasisimple ↥K := hK'.2.2
  have hKL : K ≤ L := le_trans hK'.1 inf_le_left
  have hcen := hC G L K B d hqs hchev hBel hB3 hidm hcardC hdB hdL hK' hsmall
  have hdvd : Nat.card ↥(Subgroup.center ↥K) ∣ 6 := hS G K hKq hsmall
  have h3 : Nat.Coprime 3 (Nat.card ↥(Subgroup.center ↥K)) :=
    hO G L K B d hqs hchev hBel hB3 hidm hcardC hdB hdL hK' hsmall
  have h2 : Nat.card ↥(Subgroup.center ↥K) ∣ 2 := by
    have h6 : Nat.card ↥(Subgroup.center ↥K) ∣ 2 * 3 := hdvd
    exact h3.symm.dvd_of_dvd_mul_right h6
  have hP : IsPGroup 2 ↥(Subgroup.center ↥K) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [IsPGroup.iff_card]
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  have hcenK : ∀ z : ↥(Subgroup.center ↥K), ∀ k ∈ K, k * (z : G) = (z : G) * k := by
    intro z k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨k, hk⟩)
  have hEven : Even (Nat.card ↥(Subgroup.center ↥L)) := by
    have hZne : Nat.card ↥(Subgroup.center ↥K) ≠ 1 := fun h1 =>
      hZ (Subgroup.eq_bot_of_card_eq _ h1)
    have h2dvd : 2 ∣ Nat.card ↥(Subgroup.center ↥K) := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
      · exact absurd h hZne
      · rw [h]
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
    have hzK : ((z : ↥K) : G) ∈ K := (z : ↥K).2
    have hzL : ((z : ↥K) : G) ∈ L := hKL hzK
    have hord : orderOf ((z : ↥K) : G) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    let w : ↥L := ⟨((z : ↥K) : G), hzL⟩
    have hwc : w ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact hcen _ hzK (hcenK z) g.1 g.2
    have hwo : orderOf w = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hord
    have hdv : 2 ∣ Nat.card ↥(Subgroup.center ↥L) := by
      have := orderOf_dvd_natCard (⟨w, hwc⟩ : ↥(Subgroup.center ↥L))
      rwa [Subgroup.orderOf_mk, hwo] at this
    exact even_iff_two_dvd.2 hdv
  have hAut := stdCov_aut_rank hS' hB3
  have hlist := hL G L hqs hchev hEven hAut
  obtain ⟨i, hi, ⟨e⟩⟩ := hlist
  refine ⟨hP, hcen, ?_⟩
  rcases hi with hSp | hD4 | hF4 | hU4 | hU6 | hTE6
  · exact ⟨i, Or.inl hSp, ⟨e⟩⟩
  · exact ⟨i, Or.inr (Or.inr hD4), ⟨e⟩⟩
  · exact absurd (hE G L K B d hqs ⟨i, Or.inl hF4, ⟨e⟩⟩ hBel hB3 hidm hcardC hdB hdL hK' hsmall) hZ
  · exact ⟨i, Or.inr (Or.inl hU4), ⟨e⟩⟩
  · exact absurd (hE G L K B d hqs ⟨i, Or.inr (Or.inl hU6), ⟨e⟩⟩ hBel hB3 hidm hcardC hdB hdL hK' hsmall) hZ
  · exact absurd (hE G L K B d hqs ⟨i, Or.inr (Or.inr hTE6), ⟨e⟩⟩ hBel hB3 hidm hcardC hdB hdL hK' hsmall) hZ

end CFSG.LocalAnalysis.GLTheoremA
