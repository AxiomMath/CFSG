module

public import CFSG.ClassicalInvolution.Asc77.AscS24Alpha2
public import CFSG.ClassicalInvolution.Asc77.AscT7Z23
public import CFSG.ClassicalInvolution.AschTight.S1916Local

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false

section Alpha

variable {G : Type} [Group G]

theorem oddCoreOf_eq_bot_of_alphaOf {A K : Subgroup G} (hα : alphaOf A = ⊥)
    (hle : ∀ a ∈ A, a ≠ 1 → oddCoreOf K ≤ oddCoreOf (Subgroup.centralizer ({a} : Set G))) :
    oddCoreOf K = ⊥ := by
  rw [eq_bot_iff, ← hα]
  refine le_sup_of_le_right ?_
  simp only [le_iInf_iff]
  exact fun a ha ha1 => hle a ha ha1

end Alpha

section Exact


variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem le_exactCore_of_central {c z : G} {K : Subgroup G} (hcl : IsClassicalMember p f K z)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcK : c ∈ trivialOnQuot K)
    (hOK : oddCoreOf K ≤ Subgroup.centralizer (K : Set G)) : K ≤ exactCore c K := by
  have hperf : ⁅K, K⁆ = K := by
    have := hcl.perfect
    exact Subgroup.isPerfect_iff.mp this
  exact T7Z.le_of_cover_central hperf (exactCore_le_left c K) (oddCoreIn_le K) hOK
    (exactCore_cover hcl hc2 hcK)

theorem oddCoreOf_le_oddCore_centralizer_of_layer (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {c z : G} (hc2 : c * c = 1) {K : Subgroup G}
    (hKt : K ∈ tqMembers Ω c) (hcl : IsClassicalMember p f K z)
    (hOK : oddCoreOf K ≤ Subgroup.centralizer (K : Set G))
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) (hG2 : ∀ j, D.tag j ≠ .G2)
    (hD4 : ∀ j, D.tag j ≠ .trialityD4) :
    oddCoreOf K ≤ oddCoreOf (Subgroup.centralizer ({c} : Set G)) := by
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hc2
  have hKc : K ≤ exactCore c K := le_exactCore_of_central hcl hc2' hKt.2 hOK
  have hKC : K ≤ Subgroup.centralizer ({c} : Set G) := hKc.trans (exactCore_le_centralizer c K)
  have hne : (tqMembers Ω c).Nonempty := ⟨K, hKt⟩
  have hs : SecData p f c (exactFamily Ω c) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2' hne
  have hM : exactCore c K ∈ centMembers (exactFamily Ω c) c :=
    ⟨exactCore_mem_exactFamily hKt, exactCore_le_centralizer c K⟩
  have hMY : exactCore c K ≤ centralizingLayer (exactFamily Ω c) {c} := le_centralizingLayer hM
  have hMfam : modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c K) ∈
      localFamily (exactFamily Ω c) c := ⟨(exactCore c K).subgroupOf _, ⟨_, hM, hMY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := D.fundamental _ hMfam
  set ψ := secComponentHom hs.normalizes D i with hψ
  have himg : R.map ψ = modOdd c (exactCore c K) := by
    have h1 : (R.map (D.hom i)).map (sectionQuotientHom hs.normalizes) = R.map ψ :=
      Subgroup.map_map _ _ _
    rw [← h1, ← hMR]
    exact map_sectionQuotientHom_modOddIn hs.normalizes hM
  have hexp : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · exact absurd h (hD4 i)
  obtain ⟨e⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp (D.isFundTag i)
    (D.admissible i) (hG2 i) (hD4 i) hR
  have h5 : 5 ≤ p ^ D.exp i := by rw [hexp]; exact hq
  obtain ⟨hodd, h5'⟩ := ModelFacts.odd_and_five_le_card_galoisField (p := p) hp h5
  have hzK : z ∈ K := hcl.mem
  have hzC : z ∈ Subgroup.centralizer ({c} : Set G) := hKC hzK
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hcl.orderOf_eq_two, pow_two] at this
    exact this
  have hzbar_mem : oddQuotMk c ⟨z, hzC⟩ ∈ R.map ψ := by
    rw [himg]
    exact oddQuotMk_mem_modOdd (hKc hzK) hzC
  have hzbar_ord : orderOf (oddQuotMk c ⟨z, hzC⟩) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← map_mul]
      have : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) * ⟨z, hzC⟩ = 1 :=
        Subtype.ext hz2
      rw [this, map_one]
    · intro h
      have h1 := eq_one_of_oddQuotMk_eq_one (a := c) (x := ⟨z, hzC⟩) (Subtype.ext hz2) h
      have h2 : z = 1 := congrArg Subtype.val h1
      have := hcl.orderOf_eq_two
      rw [h2, orderOf_one] at this
      exact absurd this (by decide)
  have hO : oddCoreOf (R.map ψ) = ⊥ :=
    ih8_oddCoreOf_map_eq_bot ψ hodd (by omega) e ⟨_, hzbar_mem, hzbar_ord⟩
  have hOC : oddCoreOf K ≤ Subgroup.centralizer ({c} : Set G) := (oddCoreIn_le K).trans hKC
  have hnormC : (exactCore c K).subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤
      Subgroup.normalizer
        (((oddCoreOf K).subgroupOf (Subgroup.centralizer ({c} : Set G)) : Subgroup _) : Set _) := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    have hkN := CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn K (exactCore_le_left c K hk)
    rw [Subgroup.mem_normalizer_iff] at hkN ⊢
    intro n
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
    exact hkN n
  have hOimg : modOdd c (oddCoreOf K) ≤ oddCoreOf (R.map ψ) := by
    refine CFSG.ClassicalInvolution.Disconnected.AschTight.S1916.le_oddCoreOf_of_odd ?_ ?_ ?_
    · rw [himg]
      exact Subgroup.map_mono (fun k hk => (Subgroup.mem_subgroupOf.mpr
        (hKc (oddCoreIn_le K (Subgroup.mem_subgroupOf.mp hk)))))
    · rw [himg]
      exact (Subgroup.map_mono hnormC).trans (Subgroup.le_normalizer_map _)
    · refine Odd.of_dvd_nat (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn K) ?_
      have h1 := Subgroup.card_map_dvd ((oddCoreOf K).subgroupOf
        (Subgroup.centralizer ({c} : Set G))) (oddQuotMk c)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOC).toEquiv] at h1
  rw [hO] at hOimg
  intro x hx
  have hxC : x ∈ Subgroup.centralizer ({c} : Set G) := hOC hx
  have h1 : oddQuotMk c ⟨x, hxC⟩ = 1 := by
    have : oddQuotMk c ⟨x, hxC⟩ ∈ modOdd c (oddCoreOf K) := oddQuotMk_mem_modOdd hx hxC
    exact (Subgroup.mem_bot.mp (hOimg this))
  exact ⟨⟨x, hxC⟩, oddQuotMk_eq_one_iff.mp h1, rfl⟩

end Exact

namespace Ctx


variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u g : G}
  (C : Ctx p f Ω K K' W S R R' z u g)

include C

theorem t_mem_normalizer_K : C.D.F.ρ'.r ∈ Subgroup.normalizer (K : Set G) := by
  have hst := C.hs.stand
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet C.hs.hz C.hs.hK'
  have h1 : C.D.F.ρ'.r ∈ K' := by
    have := C.D.F.ρ'.hRK.1 C.D.F.ρ'.hr
    rwa [C.hK'] at this
  exact hst.hyp.le_normalizer_of_twin C.hs.hK'.1 hst.mem C.hs.hne hzK' C.hs.hz h1

theorem oddCoreOf_K_eq_bot [IsSimpleGroup G]
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    (hL : if piSign p f then LayerLieType p f Ω C.e0 .PSL 3
      else LayerLieType p f Ω C.e0 .PSU 3) :
    oddCoreOf K = ⊥ := by
  have hst := C.hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hα := C.alphaOf_eq_bot hZ hL
  have hAuz : IsElemAbelian2 (Subgroup.closure ({u, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair C.u_sq C.z_sq C.u_ne_one C.hs.hz.ne_one C.u_ne_z C.comm_uz
  have hAuzB : Subgroup.closure ({u, z} : Set G) ≤ C.B := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact C.u_mem_B
    · exact C.z_mem_B
  have htw := ExactD.TwinPair.of_twinSet hp hq hΩ hst.mem C.hs.hz C.hs.hK' C.hs.hne.symm
  have hOK : oddCoreOf K ≤ Subgroup.centralizer (K : Set G) :=
    htw.oddCoreOf_le_centralizer_of_alphaOf_bot C.hd.hu.1 C.u_sq C.u_ne_one C.u_ne_z
      (hα _ hAuzB hAuz)
  obtain ⟨t, ht, hLt⟩ : ∃ t : CFSG.Assembly.LowTwoRank.StatedLieTag, (t = .PSL ∨ t = .PSU) ∧
      LayerLieType p f Ω C.e0 t 3 := by
    by_cases hπ : piSign p f = true
    · simp only [hπ, ↓reduceIte] at hL
      exact ⟨_, Or.inl rfl, hL⟩
    · simp only [hπ] at hL
      exact ⟨_, Or.inr rfl, hL⟩
  obtain ⟨D, hD1, i, hDt, -⟩ := exists_local_of_layerLieType hLt
  have htag : ∀ j, D.tag j = .PSL ∨ D.tag j = .PSU := fun j => by
    obtain rfl : i = j := eq_of_card_one hD1 i j
    exact hDt ▸ ht
  have hG2 : ∀ j, D.tag j ≠ .G2 := fun j => by
    rcases htag j with h | h <;> rw [h] <;> decide
  have hD4 : ∀ j, D.tag j ≠ .trialityD4 := fun j => by
    rcases htag j with h | h <;> rw [h] <;> decide
  have he0 : oddCoreOf K ≤ oddCoreOf (Subgroup.centralizer ({C.e0} : Set G)) :=
    oddCoreOf_le_oddCore_centralizer_of_layer hp hq hΩ (C.e0_sq hZ) (C.K_mem_tq_e0 hZ)
      C.K_classical hOK D hG2 hD4
  have he0z : oddCoreOf K ≤ oddCoreOf (Subgroup.centralizer ({C.e0 * z} : Set G)) := by
    have h1 := T7A.oddCoreOf_centralizer_conj C.D.F.ρ'.r C.e0
    rw [C.conj_t_e0] at h1
    rw [h1]
    have h2 := conjSub_mono (n := C.D.F.ρ'.r) he0
    rwa [← Thompson.oddCoreOf_conjSub_eq, conjSub_eq_of_mem_normalizer C.t_mem_normalizer_K]
      at h2
  have hzO : oddCoreOf K ≤ oddCoreOf (Subgroup.centralizer ({z} : Set G)) :=
    CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal
      (T7A.isSubnormal_centralizer hΩ hst.mem C.hs.hz)
  have hAze : IsElemAbelian2 (Subgroup.closure ({z, C.e0} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair C.z_sq (C.e0_sq hZ) C.hs.hz.ne_one C.e0_ne_one
      C.e0_ne_z.symm C.comm_ze
  have hAzeB : Subgroup.closure ({z, C.e0} : Set G) ≤ C.B := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact C.z_mem_B
    · exact C.e0_mem_B
  refine oddCoreOf_eq_bot_of_alphaOf (hα _ hAzeB hAze) fun a ha ha1 => ?_
  rcases Bootstrap.mem_closure_pair_cases C.z_sq (C.e0_sq hZ) C.comm_ze ha with
    rfl | rfl | rfl | rfl
  · exact absurd rfl ha1
  · exact hzO
  · exact he0
  · rw [C.comm_ze]
    exact he0z

theorem exactMembers [IsSimpleGroup G]
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    (hL : if piSign p f then LayerLieType p f Ω C.e0 .PSL 3
      else LayerLieType p f Ω C.e0 .PSU 3) :
    ExactMembers Ω := by
  have hst := C.hs.stand
  have hO : classicalInvolutionOddCore ↥K = ⊥ := by
    have h3 : (classicalInvolutionOddCore ↥K).map K.subtype = ⊥ := C.oddCoreOf_K_eq_bot hZ hL
    exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp h3
  exact exactMembers_of_oddCore_eq_bot
    ⟨K, hst.mem, fun L hL => by
      obtain ⟨h, hh⟩ := hst.trans L hL
      exact ⟨h, hh.symm⟩⟩ hst.mem hO

end Ctx

end CFSG.ClassicalInvolution.Asc77.S24
