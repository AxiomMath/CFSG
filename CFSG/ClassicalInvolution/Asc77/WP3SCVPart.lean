module

public import CFSG.ClassicalInvolution.Asc77.WP3SCVMoved
public import CFSG.ClassicalInvolution.Asc77.WP3SCVConn
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.AscIH8Red
public import CFSG.ClassicalInvolution.Asc77.WP3SCUNGa

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.SCV

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.StrongBalance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Asc77

section FromMod

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem conj_eq_of_isUniqueInvolution {N : Subgroup G} {w a : G} (hw : IsUniqueInvolution N w)
    (ha : a ∈ Subgroup.normalizer (N : Set G)) : a * w * a⁻¹ = w := by
  have hmem : a * w * a⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp ha w).mp hw.mem
  have hsq : (a * w * a⁻¹) * (a * w * a⁻¹) = 1 := by
    calc (a * w * a⁻¹) * (a * w * a⁻¹) = a * (w * w) * a⁻¹ := by group
      _ = 1 := by rw [hw.sq]; group
  rcases hw.unique _ hmem hsq with h | h
  · exfalso
    apply hw.ne_one
    have := congrArg (fun x => a⁻¹ * x * a) h
    simpa [mul_assoc] using this
  · exact h

theorem eq_one_of_sq_eq_one_of_mem_oddCoreIn {H : Subgroup G} {g : G} (hg : g ∈ oddCoreIn H)
    (h2 : g * g = 1) : g = 1 := by
  set x : ↥(oddCoreIn H) := ⟨g, hg⟩ with hx
  have hx2 : x ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact h2)
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have h3 : orderOf x ∣ Nat.card ↥(oddCoreIn H) := orderOf_dvd_natCard x
  have hodd := odd_card_oddCoreIn H
  have h4 : orderOf x ∣ Nat.gcd 2 (Nat.card ↥(oddCoreIn H)) := Nat.dvd_gcd h1 h3
  have h5 : Nat.gcd 2 (Nat.card ↥(oddCoreIn H)) = 1 :=
    Nat.coprime_two_left.mpr hodd
  rw [h5] at h4
  have h6 : x = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)
  exact congrArg Subtype.val h6

end FromMod

section Vertex

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem vertex_exists_member_of_fund (V : VertexCtx p f Ω c) (j : Fin V.D.card)
    (hG2 : V.D.tag j ≠ .G2) (hD4 : V.D.tag j ≠ .trialityD4)
    {R : Subgroup (compModel V.D j).K}
    (hR : R ∈ fundamentalSubgroups (V.D.tag j) (compModel V.D j).D) :
    ∃ N ∈ tqMembers Ω c, modOdd c (exactCore c N) = R.map (V.psi j) := by
  have hsingle : FundamentalSingleClass (V.D.tag j) (compModel V.D j).D :=
    ModelFacts.fundamentalSingleClass (V.D.tag j) (V.D.rank j) p (V.D.exp j) Fact.out
      (V.D.isFundTag j) (V.D.admissible j) hG2 hD4
  obtain ⟨M, hM, hMR⟩ := map_secComponentHom_mem_memberImages V.hs V.D j hsingle hR
  obtain ⟨N, hN, rfl⟩ := hM.1
  exact ⟨N, hN, hMR⟩

theorem vertex_exists_member_normalized (V : VertexCtx p f Ω c)
    (hT : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hBC : B ≤ Subgroup.centralizer ({c} : Set G)) {L : Subgroup G} (hL : L ∈ tqMembers Ω c)
    (hBL : ∀ x : G, ∀ hx : x ∈ B, ∀ y ∈ modOdd c (exactCore c L),
      oddQuotMk c ⟨x, hBC hx⟩ * y = y * oddQuotMk c ⟨x, hBC hx⟩) :
    ∃ L₁ ∈ tqMembers Ω c, modOdd c (exactCore c L₁) = modOdd c (exactCore c L) ∧
      B ≤ Subgroup.normalizer (L₁ : Set G) := by
  obtain ⟨w, hw⟩ := V.hΩ.classical L hL.1
  have hwE := V.involution_mem_exactCore hL hw
  have hwC := V.involution_mem_centralizer hL hw
  have hw2 : w * w = 1 := (isCentralInvolution_of_isClassicalMember hw).sq
  set Cz : Subgroup G := Subgroup.centralizer ({c} : Set G) with hCz
  have hcomm : ∀ x ∈ B, (x * w * x⁻¹) * w ∈ oddCoreIn Cz := by
    intro x hx
    have hxC := hBC hx
    have h1 := hBL x hx _ (oddQuotMk_mem_modOdd hwE hwC)
    have hmem : (x * w * x⁻¹) * w ∈ Cz :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxC hwC) (Subgroup.inv_mem _ hxC))
        hwC
    have e : (⟨(x * w * x⁻¹) * w, hmem⟩ : ↥Cz) = ⟨x, hxC⟩ * ⟨w, hwC⟩ * ⟨x, hxC⟩⁻¹ * ⟨w, hwC⟩ := rfl
    have hwb2 : oddQuotMk c ⟨w, hwC⟩ * oddQuotMk c ⟨w, hwC⟩ = 1 := by
      rw [← map_mul]
      have : (⟨w, hwC⟩ : ↥Cz) * ⟨w, hwC⟩ = 1 := Subtype.ext hw2
      rw [this, map_one]
    have h2 : oddQuotMk c ⟨(x * w * x⁻¹) * w, hmem⟩ = 1 := by
      rw [e, map_mul, map_mul, map_mul, map_inv]
      calc oddQuotMk c ⟨x, hxC⟩ * oddQuotMk c ⟨w, hwC⟩ * (oddQuotMk c ⟨x, hxC⟩)⁻¹ *
          oddQuotMk c ⟨w, hwC⟩
          = (oddQuotMk c ⟨w, hwC⟩ * oddQuotMk c ⟨x, hxC⟩) * (oddQuotMk c ⟨x, hxC⟩)⁻¹ *
            oddQuotMk c ⟨w, hwC⟩ := by rw [h1]
        _ = oddQuotMk c ⟨w, hwC⟩ * oddQuotMk c ⟨w, hwC⟩ := by group
        _ = 1 := hwb2
    exact ⟨⟨_, hmem⟩, oddQuotMk_eq_one_iff.mp h2, rfl⟩
  have hBN : B ≤ Subgroup.normalizer (oddCoreIn Cz : Set G) :=
    fun x hx => normalizer_oddCoreIn Cz (hBC hx)
  have hB2 : IsPGroup 2 ↥B := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa using hB.2 x x.2
  obtain ⟨o, ho, hcommo⟩ := exists_conj_involution_commuting (odd_card_oddCoreIn Cz) hBN hB2 hw2
    hcomm
  have hoC : o ∈ Cz := oddCoreIn_le _ ho
  have hoz : o * c * o⁻¹ = c := conj_eq_of_mem_centralizer_singleton hoC
  have hL1 : conjSub o L ∈ tqMembers Ω c := by
    refine ⟨V.hΩ.conjInvariant o L hL.1, ?_⟩
    have h := trivialOnQuot_conjSub hL.2 o
    rwa [hoz] at h
  have hw1 : IsClassicalMember p f (conjSub o L) (o * w * o⁻¹) := hw.conj o
  refine ⟨conjSub o L, hL1, ?_, fun x hx => ?_⟩
  · have h1 : exactCore c (conjSub o L) = conjSub o (exactCore c L) := by
      have := exactCore_conjSub o c L
      rwa [hoz] at this
    rw [h1]
    exact modOdd_conjSub_of_mem_oddCoreIn ho _
  · exact mem_normalizer_of_commutes_involution V.hΩ.conjInvariant hT hL1.1
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember V.hp V.hq hw1) (hcommo x hx)

end Vertex

section Partner

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {z t z' : G}

theorem zt_t_eq (hs : ChainFrameSetting p f Ω K J K' z t z') : t = z * (z * t) := by
  have hz2 : z * z = 1 := hs.frame.hz.sq
  rw [← mul_assoc, hz2, one_mul]

theorem partner_member (hs : ChainFrameSetting p f Ω K J K' z t z')
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) (j : Fin D.card)
    (hG2 : D.tag j ≠ .G2) (hD4 : D.tag j ≠ .trialityD4) {R_K : Subgroup (compModel D j).K}
    (hmodK : R_K.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
      modOdd (z * t) (exactCore (z * t) K))
    {S : Subgroup (compModel D j).K}
    (hS : S ∈ fundamentalSubgroups (D.tag j) (compModel D j).D) (hc : Commutes R_K S) :
    ∃ N ∈ Ω, z ∈ trivialOnQuot N ∧ t ∈ trivialOnQuot N ∧
      modOdd (z * t) (exactCore (z * t) N) =
        S.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) := by
  have hΩ := hs.hyp
  have hfd := hs.frame
  let V : VertexCtx p f Ω (z * t) := ztVertex hs D
  have hzC := zt_z_mem hs
  have hKcl : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hfd.mem hfd.hz
  obtain ⟨N₀, hN₀, hmod₀⟩ := vertex_exists_member_of_fund V j hG2 hD4 hS
  have hzK : oddQuotMk (z * t) ⟨z, hzC⟩ ∈ R_K.map (V.psi j) := by
    have h1 : R_K.map (V.psi j) = modOdd (z * t) (exactCore (z * t) K) := hmodK
    rw [h1]
    exact oddQuotMk_mem_modOdd (V.involution_mem_exactCore (zt_memK hs) hKcl) hzC
  have hcomm₀ : ∀ y ∈ modOdd (z * t) (exactCore (z * t) N₀),
      oddQuotMk (z * t) ⟨z, hzC⟩ * y = y * oddQuotMk (z * t) ⟨z, hzC⟩ := by
    intro y hy
    rw [hmod₀] at hy
    obtain ⟨s, hs', rfl⟩ := hy
    obtain ⟨r, hr, hrz⟩ := hzK
    rw [← hrz, ← map_mul, ← map_mul]
    exact congrArg (V.psi j) (hc r hr s hs')
  have hz2 : z * z = 1 := hfd.hz.sq
  have hBel : IsElemAbelian 2 (Subgroup.zpowers z) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2', one_zpow]
  have hBC : Subgroup.zpowers z ≤ Subgroup.centralizer ({z * t} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hzC
  obtain ⟨N₁, hN₁, hmod₁, hBN₁⟩ := vertex_exists_member_normalized V hs.noTwins hBel hBC hN₀ (by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have e : (⟨z ^ k, hBC hx⟩ : ↥(Subgroup.centralizer ({z * t} : Set G))) =
        (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z * t} : Set G))) ^ k :=
      Subtype.ext (by simp)
    rw [e, map_zpow]
    exact ((Commute.zpow_left (hcomm₀ y hy) k).eq))
  obtain ⟨w₁, hw₁⟩ := hΩ.classical N₁ hN₁.1
  have hzN₁ : z ∈ Subgroup.normalizer (N₁ : Set G) := hBN₁ (Subgroup.mem_zpowers z)
  have hz_tq : z ∈ trivialOnQuot N₁ := by
    refine mem_trivialOnQuot_of_centralizes_modOdd hw₁ (zt_hc2 hs) hN₁.2 hzC hzN₁ ?_
    intro y hy
    rw [hmod₁] at hy
    exact hcomm₀ y hy
  have ht_tq : t ∈ trivialOnQuot N₁ := by
    rw [zt_t_eq hs]
    exact Subgroup.mul_mem _ hz_tq hN₁.2
  refine ⟨N₁, hN₁.1, hz_tq, ht_tq, ?_⟩
  have h2 : modOdd (z * t) (exactCore (z * t) N₀) =
      S.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) := hmod₀
  exact hmod₁.trans h2

theorem partner_bound (hs : ChainFrameSetting p f Ω K J K' z t z')
    (hThird : ∀ N ∈ Ω, N ≠ K → N ≠ J → z ∈ trivialOnQuot N → t ∈ trivialOnQuot N →
      IsUniqueInvolution N (z * t))
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) (j : Fin D.card)
    (hG2 : D.tag j ≠ .G2) (hD4 : D.tag j ≠ .trialityD4)
    {R_K R_J : Subgroup (compModel D j).K}
    (hRK : R_K ∈ fundamentalSubgroups (D.tag j) (compModel D j).D)
    (hRJ : R_J ∈ fundamentalSubgroups (D.tag j) (compModel D j).D)
    (hmodK : R_K.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
      modOdd (z * t) (exactCore (z * t) K))
    (hmodJ : R_J.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
      modOdd (z * t) (exactCore (z * t) J)) :
    ∃ a b : Subgroup (compModel D j).K,
      ∀ S ∈ Partners (fundamentalSubgroups (D.tag j) (compModel D j).D) R_K, S = a ∨ S = b := by
  classical
  let V : VertexCtx p f Ω (z * t) := ztVertex hs D
  set ψ := secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j with hψ
  have hker : ψ.ker ≤ Subgroup.center (compModel D j).K := V.psi_ker j
  have hperf : ∀ S ∈ fundamentalSubgroups (D.tag j) (compModel D j).D, S ≤ ⁅S, S⁆ :=
    fun S hS => (V.fund_perfect j hD4 hS).ge
  have key : ∀ S ∈ Partners (fundamentalSubgroups (D.tag j) (compModel D j).D) R_K,
      S ≠ R_J → ∃ N ∈ Ω, IsUniqueInvolution N (z * t) ∧
        modOdd (z * t) (exactCore (z * t) N) = S.map ψ := by
    intro S hS hSJ
    obtain ⟨N, hNΩ, hzN, htN, himg⟩ := partner_member hs D j hG2 hD4 hmodK hS.1 hS.2.2
    refine ⟨N, hNΩ, hThird N hNΩ ?_ ?_ hzN htN, himg⟩
    · intro hNK
      rw [hNK] at himg
      exact hS.2.1 (ih8_eq_of_map_eq ψ hker (hperf S hS.1) (hperf R_K hRK)
        (himg.symm.trans hmodK.symm))
    · intro hNJ
      rw [hNJ] at himg
      exact hSJ (ih8_eq_of_map_eq ψ hker (hperf S hS.1) (hperf R_J hRJ)
        (himg.symm.trans hmodJ.symm))
  by_cases h0 : ∃ S₀ ∈ Partners (fundamentalSubgroups (D.tag j) (compModel D j).D) R_K,
      S₀ ≠ R_J
  · obtain ⟨S₀, hS₀, hS₀J⟩ := h0
    refine ⟨R_J, S₀, fun S hS => ?_⟩
    by_cases hSJ : S = R_J
    · exact Or.inl hSJ
    · right
      obtain ⟨N, hNΩ, hNc, hNimg⟩ := key S hS hSJ
      obtain ⟨N₀, hN₀Ω, hN₀c, hN₀img⟩ := key S₀ hS₀ hS₀J
      have hNN : N₀ = N := hs.noTwins N hNΩ N₀ ⟨hN₀Ω, z * t, hNc, hN₀c⟩
      subst hNN
      exact ih8_eq_of_map_eq ψ hker (hperf S hS.1) (hperf S₀ hS₀.1) (hNimg.symm.trans hN₀img)
  · push Not at h0
    exact ⟨R_J, R_J, fun S hS => Or.inl (h0 S hS)⟩

end Partner

end CFSG.ClassicalInvolution.Asc77.SCV
