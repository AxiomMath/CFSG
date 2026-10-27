module

public import CFSG.ClassicalInvolution.RouteD.TwinYSetup
public import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsRankFour
public import CFSG.ClassicalInvolution.Asc77.AscE186CentA

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Open (classicalInvolutionOddCore)

section Sylow

variable {G : Type} [Group G]

theorem exists_conj_sylow_centralizes {N M R : Subgroup G} {z : G} (hN : Odd (Nat.card N))
    (hMN : ∀ x ∈ M, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hz : z * z = 1)
    (hzN : ∀ n ∈ N, z * n * z⁻¹ ∈ N) (hzM : ∀ x ∈ M, z * x * z⁻¹ * x⁻¹ ∈ N)
    (hR : IsSylow2In R M) :
    ∃ o ∈ N, conjSub o R ≤ Subgroup.centralizer ({z} : Set G) := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  obtain ⟨n, hnN, hfix⟩ := exists_conj_fixed_of_isPGroup (A := R) (N := N) hR.2.1 hN
    (fun x hx m hm => hMN x (hR.1 hx) m hm) hz hzN (fun x hx => by
      have h1 := hzM x (hR.1 hx)
      rw [hzinv] at h1
      simpa [mul_assoc] using h1)
  refine ⟨n⁻¹, N.inv_mem hnN, ?_⟩
  intro y hy
  have h1 : n * y * n⁻¹ ∈ R := by
    have := mem_conjSub_iff.mp hy
    simpa using this
  have e1 : (n * y * n⁻¹) * (n * z * n⁻¹) = (n * z * n⁻¹) * (n * y * n⁻¹) := by
    have := hfix _ h1
    calc (n * y * n⁻¹) * (n * z * n⁻¹)
        = ((n * y * n⁻¹) * (n * z * n⁻¹) * (n * y * n⁻¹)⁻¹) * (n * y * n⁻¹) := by group
      _ = (n * z * n⁻¹) * (n * y * n⁻¹) := by rw [this]
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc y * z = n⁻¹ * ((n * y * n⁻¹) * (n * z * n⁻¹)) * n := by group
    _ = n⁻¹ * ((n * z * n⁻¹) * (n * y * n⁻¹)) * n := by rw [e1]
    _ = z * y := by group

end Sylow

section Omega

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_omegaNbr_of_sylow_centralizes (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K J R : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hne : J ≠ K)
    {z : G} (hz : IsUniqueInvolution K z) (hR : IsSylow2In R J) (hRset : R ∈ RSet Ω)
    (hRc : R ≤ Subgroup.centralizer ({z} : Set G)) : J ∈ omegaNbr Ω K := by
  have h8 := hΩ.eight_le_of_mem_RSet hp hRset
  exact ⟨hJ, hne, R, hRset, hR.1, hΩ.le_normalizer_of_le_centralizer hp hq hK hJ hne.symm hz hR.1
    hR.2.1 (by omega) hRc⟩

theorem exists_conj_commutes_of_comm_mod (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmega p f Ω)
    {K T M N : Subgroup G} {z : G} (hK : K ∈ Ω) (hT : T ∈ Ω) (hM : M ∈ Ω)
    (hKz : IsUniqueInvolution K z) (hTz : IsUniqueInvolution T z) (hN : Odd (Nat.card N))
    (hMN : ∀ x ∈ M, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hzN : ∀ n ∈ N, z * n * z⁻¹ ∈ N)
    (hzM : ∀ x ∈ M, z * x * z⁻¹ * x⁻¹ ∈ N) :
    ∃ o ∈ N, conjSub o M ∈ Ω ∧ (conjSub o M = K ∨ Commutes K (conjSub o M)) ∧
      (conjSub o M = T ∨ Commutes T (conjSub o M)) := by
  have hz2 : z * z = 1 := hKz.sq
  have hΩm : HypOmegaMod p f Ω := hΩ.toMod
  obtain ⟨R, hRset, hRM, -⟩ := exists_mem_RSet_ge hM
    (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G)) bot_le
  obtain ⟨o, hoN, hoc⟩ := exists_conj_sylow_centralizes hN hMN hz2 hzN hzM hRM
  have hM' : conjSub o M ∈ Ω := hΩ.conjInvariant o M hM
  have hR'syl : IsSylow2In (conjSub o R) (conjSub o M) := IsSylow2In.conj hRM o
  have hR'set : conjSub o R ∈ RSet Ω := mem_RSet_of_isSylow2In hM' hR'syl
  refine ⟨o, hoN, hM', ?_, ?_⟩
  · by_cases hMK : conjSub o M = K
    · exact Or.inl hMK
    · exact Or.inr (AscE186.commutes_of_mem_omegaNbr hp hq hΩ hK
        (mem_omegaNbr_of_sylow_centralizes hp hq hΩm hK hM' hMK hKz hR'syl hR'set hoc))
  · by_cases hMT : conjSub o M = T
    · exact Or.inl hMT
    · exact Or.inr (AscE186.commutes_of_mem_omegaNbr hp hq hΩ hT
        (mem_omegaNbr_of_sylow_centralizes hp hq hΩm hT hM' hMT hTz hR'syl hR'set hoc))

end Omega

section Layer

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_conj_layer_of_comm_mod (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmega p f Ω)
    {K T M : Subgroup G} {z u : G} (hK : K ∈ Ω) (hT : T ∈ Ω) (hKz : IsUniqueInvolution K z)
    (hTz : IsUniqueInvolution T z) (hKu : ¬ K ≤ Subgroup.centralizer ({u} : Set G))
    (hTu : ¬ T ≤ Subgroup.centralizer ({u} : Set G))
    (hzu : z ∈ Subgroup.centralizer ({u} : Set G)) (hM : M ∈ centralizingMembers Ω {u})
    (hzM : ∀ x ∈ M, z * x * z⁻¹ * x⁻¹ ∈ oddCoreIn (locLayer Ω u)) :
    ∃ o ∈ oddCoreIn (locLayer Ω u), conjSub o M ∈ centralizingMembers Ω {z} ∧
      conjSub o M ∈ centralizingMembers Ω {u} ∧ conjSub o M ≠ K ∧ conjSub o M ≠ T ∧
      locImg Ω u (conjSub o M) = locImg Ω u M := by
  set Y := locLayer Ω u with hY
  have hMY : M ≤ Y := le_centralizingLayer hM
  have hzNorm : z ∈ Subgroup.normalizer (oddCoreIn Y : Set G) :=
    mem_normalizer_oddCoreIn_centralizingLayer hΩ.conjInvariant hzu
  have hzN : ∀ n ∈ oddCoreIn Y, z * n * z⁻¹ ∈ oddCoreIn Y := fun n hn =>
    (Subgroup.mem_normalizer_iff.mp hzNorm n).mp hn
  obtain ⟨o, hoN, hM', hKc, hTc⟩ := exists_conj_commutes_of_comm_mod hp hq hΩ hK hT hM.1 hKz hTz
    (odd_card_oddCoreIn Y) (fun x hx n hn => conj_mem_oddCoreIn (hMY hx) hn) hzN hzM
  have hoY : o ∈ Y := oddCoreIn_le Y hoN
  have hoC : o ∈ Subgroup.centralizer ({u} : Set G) :=
    centralizingLayer_le_centralizer Ω {u} hoY
  have hM'u : conjSub o M ≤ Subgroup.centralizer ({u} : Set G) := by
    intro y hy
    have h1 : o⁻¹ * y * o ∈ M := mem_conjSub_iff.mp hy
    have h2 : o⁻¹ * y * o ∈ Subgroup.centralizer ({u} : Set G) := hM.2 h1
    have e : y = o * (o⁻¹ * y * o) * o⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hoC h2) (inv_mem hoC)
  have hne : ∀ {L : Subgroup G}, ¬ L ≤ Subgroup.centralizer ({u} : Set G) → conjSub o M ≠ L :=
    fun hL h => hL (h ▸ hM'u)
  have hMK : conjSub o M ≠ K := hne hKu
  have hMT : conjSub o M ≠ T := hne hTu
  refine ⟨o, hoN, ⟨hM', fun x hx => ?_⟩, ⟨hM', hM'u⟩, hMK, hMT, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hKc.resolve_left hMK) z hKz.mem x hx).symm
  · have hmk : locMk Ω u ⟨o, hoY⟩ = 1 :=
      (QuotientGroup.eq_one_iff (⟨o, hoY⟩ : ↥(locLayer Ω u))).mpr
        (mem_oddCoreOf_iff.mp hoN).2
    rw [locImg_conjSub_layer M ⟨o, hoY⟩, hmk]
    ext x
    simp

end Layer

section Twin

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K T : Subgroup G} {z : G}

theorem TwinElt.exists_conj_layer_of_comm_mod (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmega p f Ω)
    (e : TwinElt K T z) (hK : K ∈ Ω) (hT : T ∈ Ω) (hKz : IsClassicalMember p f K z)
    (hTz : IsClassicalMember p f T z) (hKT : Commutes K T) {M : Subgroup G}
    (hM : M ∈ centralizingMembers Ω {e.u})
    (hzM : ∀ x ∈ M, z * x * z⁻¹ * x⁻¹ ∈ oddCoreIn (locLayer Ω e.u)) :
    ∃ o ∈ oddCoreIn (locLayer Ω e.u), conjSub o M ∈ centralizingMembers Ω {z} ∧
      conjSub o M ∈ centralizingMembers Ω {e.u} ∧ conjSub o M ≠ K ∧ conjSub o M ≠ T ∧
      locImg Ω e.u (conjSub o M) = locImg Ω e.u M := by
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp hq
  have hzu : z ∈ Subgroup.centralizer ({e.u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (e.u_comm_z (le_centralizer_of_isClassicalMember hKz)
        (le_centralizer_of_isClassicalMember hTz)).symm
  exact TwinY.exists_conj_layer_of_comm_mod hp hq hΩ hK hT
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hKz)
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hTz)
    (e.not_le_centralizer_left hKz (hΩ.exact K hK) hodd hKT)
    (e.not_le_centralizer_right hTz (hΩ.exact T hT) hodd hKT) hzu hM hzM

theorem TwinElt.exists_layer_member_of_comm_mod (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmega p f Ω) (e : TwinElt K T z) (hK : K ∈ Ω) (hT : T ∈ Ω)
    (hKz : IsClassicalMember p f K z) (hTz : IsClassicalMember p f T z) (hKT : Commutes K T)
    {M : Subgroup G} (hM : M ∈ centralizingMembers Ω {e.u})
    (hzM : ∀ x ∈ M, z * x * z⁻¹ * x⁻¹ ∈ oddCoreIn (locLayer Ω e.u)) :
    ∃ N ∈ centralizingMembers Ω {z}, N ≠ K ∧ N ≠ T ∧
      N ∈ centralizingMembers Ω {e.u} ∧ locImg Ω e.u N = locImg Ω e.u M := by
  obtain ⟨o, -, hNz, hNu, hNK, hNT, himg⟩ :=
    e.exists_conj_layer_of_comm_mod hp hq hΩ hK hT hKz hTz hKT hM hzM
  exact ⟨conjSub o M, hNz, hNK, hNT, hNu, himg⟩

end Twin

end CFSG.ClassicalInvolution.RouteD.TwinY
