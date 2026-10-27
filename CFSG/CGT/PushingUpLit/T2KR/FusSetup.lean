module

public import CFSG.CGT.PushingUpLit.T2KR.FusFinal
public import CFSG.CGT.PushingUpLit.T2KR.Assemble

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75 CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.JonesParshall
open scoped commutatorElement LinearAlgebra.Projectivization
open MData (QM)

@[expose] def Print614 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) (D : Subgroup G) (g : G)
    (hE1 : FooteNonsolvableSimple) (hs : Sit64 G L M T n D g),
    PairFacts (MData.ofSec6 hE1 hs.sec6) (normIn (QOf L M) (Aof L M g))
      (normIn (Aof L M g) (QOf L M)) D → Nat.card D = 4 →
      ∀ x ∈ D, x ∉ blockU L → ∀ r ∈ normIn (Aof L M g) (QOf L M), r ∈ L → r ∉ QOf L M →
        ∀ h : G, h * (x * r) * h⁻¹ ∉ blockU L

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_two_of_sq_eq_one {B : Subgroup G} (hB : ∀ y ∈ B, y * y = 1) : IsPGroup 2 B :=
  fun y => ⟨1, Subtype.ext (by simpa [pow_two] using hB y y.2)⟩

theorem exists_fusConfig (h614 : Print614) (hE1 : FooteNonsolvableSimple)
    {L M T : Subgroup G} {n : ℕ} {D : Subgroup G} {g : G} (hs : Sit64 G L M T n D g)
    (hP : PairFacts (MData.ofSec6 hE1 hs.sec6) (normIn (QOf L M) (Aof L M g))
      (normIn (Aof L M g) (QOf L M)) D) (hD4 : Nat.card D = 4) :
    ∃ (T' : Subgroup G) (x ε b : G), CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ ∧
      FusConfig (MData.ofSec6 hE1 hs.sec6) T' x ε b g := by
  classical
  set H := MData.ofSec6 hE1 hs.sec6 with hH
  set B := normIn (Aof L M g) (QOf L M) with hB
  have hD0 : D ≠ ⊥ := by
    rintro rfl
    simp at hD4
  rcases hP.step66 with hBLQ | ⟨hD', -⟩
  swap
  · exact absurd hD' hD0
  obtain ⟨hDE, -, hn⟩ := hP.step610 hBLQ
  obtain ⟨hDV, -, -⟩ := hP.step611 hBLQ
  have hQD := hP.relIndex_Q_eq hBLQ
  have hVQ : blockU L ≤ QM L M := H.blockU_le_QM
  have hF : Nat.card (Fq n) = 4 := by
    rw [GaloisField.card 2 n H.n_ne_zero, hn]
    norm_num
  have hVcard : Nat.card ↥(blockU L) = 16 := by
    rw [H.card_V, hF]; norm_num
  have hQcard : Nat.card ↥(QM L M) = 32 := by
    have := PairFacts.relIndex_mul_card_of_le hP.D_le_Q
    rw [hQD, hD4] at this
    omega
  have hVQrel : (blockU L).relIndex (QM L M) = 2 := by
    have := PairFacts.relIndex_mul_card_of_le hVQ
    rw [hVcard, hQcard] at this
    omega
  obtain ⟨x, hxD, hxV⟩ : ∃ x ∈ D, x ∉ blockU L := by
    by_contra hcon
    push Not at hcon
    have hle : D ≤ blockU L := hcon
    have h1 : Nat.card ↥(D ⊓ blockU L) = Nat.card ↥D := by rw [inf_eq_left.2 hle]
    omega
  have hxB : x ∈ B := hP.D_le_B hxD
  have hx2 : x * x = 1 := hP.B_sq x hxB
  have hxQ : x ∈ QM L M := hP.D_le_Q hxD
  have hQeq : ∀ q ∈ QM L M, q ∈ blockU L ∨ x⁻¹ * q ∈ blockU L := by
    intro q hq
    by_cases hqV : q ∈ blockU L
    · exact Or.inl hqV
    · exact Or.inr (inv_mul_mem_of_relIndex_two hVQrel hxQ hq hxV hqV)
  have hxg : x * g = g * x := Subgroup.mem_centralizer_iff.1 hs.g_mem x hxD
  have hgx : g⁻¹ * x⁻¹ = x⁻¹ * g⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hxg]
  have hBU : ∀ a ∈ B, g⁻¹ * a * g ∈ blockU L ∨ g⁻¹ * (x⁻¹ * a) * g ∈ blockU L := by
    intro a ha
    have haA : g⁻¹ * a * g ∈ QM L M := (mem_conjSubgroup).1 ha.1
    rcases hQeq _ haA with h | h
    · exact Or.inl h
    · right
      have e : x⁻¹ * (g⁻¹ * a * g) = g⁻¹ * (x⁻¹ * a) * g := by
        calc x⁻¹ * (g⁻¹ * a * g) = (x⁻¹ * g⁻¹) * a * g := by group
          _ = (g⁻¹ * x⁻¹) * a * g := by rw [hgx]
          _ = g⁻¹ * (x⁻¹ * a) * g := by group
      rw [← e]; exact h
  have hxLQ : x ∈ L ⊔ QM L M := (le_sup_right : QM L M ≤ L ⊔ QM L M) hxQ
  set E : Subgroup G := B ⊓ (L ⊔ QM L M) with hE
  have hxE : x ∈ E := ⟨hxB, hxLQ⟩
  obtain ⟨e₀, he₀E, he₀D⟩ : ∃ e ∈ E, e ∉ D := by
    by_contra hcon
    push Not at hcon
    have hED : E ≤ D := hcon
    have := Subgroup.relIndex_eq_one.2 hED
    omega
  have he₀B : e₀ ∈ B := he₀E.1
  obtain ⟨ε, hεE, hεD, hεg⟩ : ∃ ε ∈ E, ε ∉ D ∧ g⁻¹ * ε * g ∈ blockU L := by
    rcases hBU e₀ he₀B with h | h
    · exact ⟨e₀, he₀E, he₀D, h⟩
    · refine ⟨x⁻¹ * e₀, E.mul_mem (E.inv_mem hxE) he₀E, ?_, h⟩
      intro hmem
      apply he₀D
      have : e₀ = x * (x⁻¹ * e₀) := by group
      rw [this]
      exact D.mul_mem hxD hmem
  have hεB : ε ∈ B := hεE.1
  have hε2 : ε * ε = 1 := hP.B_sq ε hεB
  have hεQ : ε ∉ QM L M := fun h => hεD (by rw [← hP.B_inf_Q]; exact ⟨hεB, h⟩)
  have hεM : ε ∈ M := hP.B_le_M hεB
  have hεLQ : ε ∈ L ⊔ QM L M := hεE.2
  have hεx : ε * x = x * ε := hP.B_comm ε hεB x hxB
  have hεL : ε ∈ L := by
    by_contra hεL
    obtain ⟨l, hl, q, hq, hlq⟩ := H.mem_LQ_iff.1 hεLQ
    rcases hQeq q hq with hqV | hxqV
    · exact hεL (by rw [← hlq]; exact L.mul_mem hl (CFSG.CGT.PushingUpLit.blockU_le L hqV))
    · obtain ⟨r, hr⟩ : ∃ r, r = ε * x := ⟨_, rfl⟩
      have hv := CFSG.CGT.PushingUpLit.blockU_le L hxqV
      have hcomm : x * (x⁻¹ * q) = (x⁻¹ * q) * x := H.Q_comm x hxQ _ (H.blockU_le_QM hxqV)
      have hrL : r ∈ L := by
        have e : l * q * x = l * (x⁻¹ * q) := by
          have hq' : q = x * (x⁻¹ * q) := by group
          calc l * q * x = l * (x * (x⁻¹ * q)) * x := by rw [← hq']
            _ = l * ((x⁻¹ * q) * x) * x := by rw [hcomm]
            _ = l * (x⁻¹ * q) * (x * x) := by group
            _ = l * (x⁻¹ * q) := by rw [hx2, mul_one]
        rw [hr, ← hlq, e]
        exact L.mul_mem hl hv
      have hrB : r ∈ B := by rw [hr]; exact B.mul_mem hεB hxB
      have hrQ : r ∉ QM L M := by
        intro h
        apply hεQ
        have : ε = r * x⁻¹ := by rw [hr]; group
        rw [this]
        exact (QM L M).mul_mem h ((QM L M).inv_mem hxQ)
      have hxr : x * r = ε := by
        rw [hr]
        calc x * (ε * x) = x * (x * ε) := by rw [hεx]
          _ = (x * x) * ε := by group
          _ = ε := by rw [hx2, one_mul]
      have := h614 G L M T n D g hE1 hs hP hD4 x hxD hxV r hrB hrL hrQ g⁻¹
      apply this
      rw [hxr]
      simpa using hεg
  obtain ⟨b₀, hb₀B, hb₀E⟩ : ∃ b ∈ B, b ∉ E := by
    by_contra hcon
    push Not at hcon
    have hBE : B ≤ E := hcon
    have h1 : E.relIndex B = 1 := Subgroup.relIndex_eq_one.2 hBE
    have h2 : E.relIndex B = 2 := hP.relIndex_E hBLQ
    omega
  obtain ⟨b, hbB, hbE, hbg⟩ : ∃ b ∈ B, b ∉ E ∧ g⁻¹ * b * g ∈ blockU L := by
    rcases hBU b₀ hb₀B with h | h
    · exact ⟨b₀, hb₀B, hb₀E, h⟩
    · refine ⟨x⁻¹ * b₀, B.mul_mem (B.inv_mem hxB) hb₀B, ?_, h⟩
      intro hmem
      apply hb₀E
      have : b₀ = x * (x⁻¹ * b₀) := by group
      rw [this]
      exact E.mul_mem hxE hmem
  have hQL : QM L M ⊓ L ≤ blockU L := by
    have hO : oTwoIn L = blockU L := by
      refine H.nat.oTwoIn_eq_blockU_of_sq_mem (r := ε) hεL ?_ ?_
      · intro hεO
        apply hεQ
        rw [← H.nat.inf_centralizer_blockU] at hεO
        exact ⟨H.le hεO.1, hεO.2⟩
      · rw [pow_two, hε2]
        exact (blockU L).one_mem
    intro y hy
    have hy' : y ∈ L ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨hy.2, hy.1.2⟩
    rw [H.nat.inf_centralizer_blockU, hO] at hy'
    exact hy'
  have hB2 : IsPGroup 2 B := isPGroup_two_of_sq_eq_one hP.B_sq
  obtain ⟨k, hkM, hk⟩ := exists_conj_le_of_isPGroup hs.sec6.sec4.sylow hB2 hP.B_le_M
  set T' : Subgroup G := T.map (MulAut.conj k⁻¹).toMonoidHom with hT'
  have hBT' : B ≤ T' := by
    intro y hy
    refine ⟨k * y * k⁻¹, hk ⟨y, hy, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hT'M : T' ≤ M := by
    rintro _ ⟨t, ht, rfl⟩
    have htM : t ∈ M := hs.sec6.sec4.sylow.le ht
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact M.mul_mem (M.mul_mem (M.inv_mem hkM) htM) hkM
  have hT'2 : IsPGroup 2 T' := hs.sec6.sec4.sylowG.isPGroup.map _
  have hT'syl : CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
    rw [hT', card_map_conj]
    exact hs.sec6.sec4.sylowG.card_eq
  exact ⟨T', x, ε, b, hT'syl,
    { n_eq := hn
      QL := hQL
      Q_eq := hQeq
      x_Q := hxQ
      x_V := hxV
      x_sq := hx2
      ε_L := hεL
      ε_Q := hεQ
      ε_sq := hε2
      b_M := hP.B_le_M hbB
      b_sq := hP.B_sq b hbB
      b_LQ := fun h => hbE ⟨hbB, h⟩
      εb := hP.B_comm ε hεB b hbB
      xb := hP.B_comm x hxB b hbB
      T'_M := hT'M
      T'_2 := hT'2
      x_T := hBT' hxB
      ε_T := hBT' hεB
      b_T := hBT' hbB
      g_ε := hεg
      g_b := hbg }⟩

theorem print612_of_614 (h614 : Print614) : Print612 := by
  intro G _ _ L M T n D g hE1 hs hP hD4
  obtain ⟨T', x, ε, b, hT', c⟩ := exists_fusConfig h614 hE1 hs hP hD4
  have : IsSimpleGroup G := hs.sec6.sec4.hyp.simple
  have hG2 : 2 < Nat.card G := by
    have h60 := hs.sec6.sec4.hyp.natBlock.sixty_le_card
    have := Subgroup.card_le_card_group L
    omega
  exact fusion_false hs.sec6 hG2 hT' c

end CFSG.CGT.PushingUpLit.T2KR
