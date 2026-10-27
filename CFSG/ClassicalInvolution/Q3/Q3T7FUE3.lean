module

public import CFSG.ClassicalInvolution.Q3.Q3T7FUE2
public import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.AscE187EndB

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.T7FU

variable {MT : CFSG.ClassicalInvolution.Uniform.MemberType}
open CFSG.ClassicalInvolution.Q3.Q3T7M (omegaNbr_subset_kPerp_of_twin mem_kPerp_of_twin
  omegaStarDiff_subset_of_twin l6_3 le_of_sq_mem_of_oddGen odd_mem_of_mem_sup_central
      oddGen_conjSub)
open CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
    (HypOmegaMod L6_2 l6_2 L6_7 l6_7_proved L6_10 l6_10_proved
  L6_11 l6_11_proved L6_9 l6_9_proved)

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement MatrixGroups
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
section Finite
variable [Finite G]

omit [Finite G] in

theorem isClassicalMember_of_twin (hΩ : HM MT Ω) {M : Subgroup G} {t : G}
    (hM : M ∈ Ω) (hMt : IsUniqueInvolution M t) : Uniform.IsClassicalMemberU MT M t := by
  obtain ⟨z', hz'⟩ := hΩ.classical M hM
  have hzsq : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz'.orderOf_eq_two, pow_two] at this
  have hzne : z' ≠ 1 := by
    intro h
    have := hz'.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  obtain rfl : z' = t := (hMt.unique z' hz'.mem hzsq).resolve_left hzne
  exact hz'

theorem exists_twHom (hΩ : HM MT Ω) {M : Subgroup G} {t : G} (hM : M ∈ Ω)
    (hMt : IsUniqueInvolution M t) :
    ∃ ψ : ↥M →* ↥(twImage t M), Function.Surjective ψ ∧
      ψ.ker = classicalInvolutionOddCore ↥M ∧
      ∀ x : ↥M, ((ψ x : ↥(twImage t M)) : TwQ t) =
        twMk t ⟨(x : G), le_TwC_of_isUniqueInvolution hMt x.2⟩ :=
  E187C.exists_twHom_of hMt (isClassicalMember_of_twin hΩ hM hMt).subnormal

omit [Finite G] in

theorem isSubnormal_twImage (hΩ : HM MT Ω) {M : Subgroup G} {t : G}
    (hM : M ∈ Ω) (hMt : IsUniqueInvolution M t) : IsSubnormal (twImage t M) ⊤ := by
  have hMC : M ≤ TwC t := le_TwC_of_isUniqueInvolution hMt
  have hz' := isClassicalMember_of_twin hΩ hM hMt
  have h1 : IsSubnormal (M.subgroupOf (TwC t)) ⊤ :=
    (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hMC).mpr hz'.subnormal
  have h2 := CFSG.ComponentClassification.Components.chain_map (twMk t) h1
  rwa [Subgroup.map_top, MonoidHom.range_eq_top.mpr (twMk_surjective t)] at h2

theorem mem_oddCore_of_coe_mem_oddCoreOf (hΩ : HM MT Ω) {M : Subgroup G} {t : G}
    (hM : M ∈ Ω) (hMt : IsUniqueInvolution M t) {x : ↥(TwC t)} (hx : (x : G) ∈ oddCoreOf M) :
    x ∈ classicalInvolutionOddCore ↥(TwC t) := by
  obtain ⟨h, hxN⟩ := mem_oddCoreOf_iff.mp hx
  obtain ⟨_, h'⟩ := (CFSG.ComponentClassification.OddCore.subnormal_mem_iff
    (isClassicalMember_of_twin hΩ hM hMt).subnormal (x : G) h).mp hxN
  exact h'

theorem commutes_twImage (hΩ : HM MT Ω) {M J : Subgroup G} {t : G} (hM : M ∈ Ω)
    (hJ : J ∈ Ω) (hMJ : M ≠ J) (hMt : IsUniqueInvolution M t) (hJt : IsUniqueInvolution J t) :
    Commutes (twImage t M) (twImage t J) := by
  have hc := hΩ.comm_le_oddCore_of_twin hM hJ hMJ hMt hJt
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have ha' : (a : G) ∈ M := Subgroup.mem_subgroupOf.mp ha
  have hb' : (b : G) ∈ J := Subgroup.mem_subgroupOf.mp hb
  have h1 : ((⁅a, b⁆ : ↥(TwC t)) : G) ∈ oddCoreOf M :=
    (hc (Subgroup.commutator_mem_commutator ha' hb')).1
  have h2 : twMk t ⁅a, b⁆ = 1 :=
    (twMk_eq_one_iff t _).mpr (mem_oddCore_of_coe_mem_oddCoreOf hΩ hM hMt h1)
  rw [map_commutatorElement] at h2
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

end Finite
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G]

theorem exists_W_of_hypOmega {Ω : Set (Subgroup G)}
    (hΩ : HM MT Ω) (S : Sylow 2 G) :
    ∃ W ∈ WSet Ω, W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W := by
  obtain ⟨η, hη, hinv⟩ := (l6_9_proved G Ω hΩ S).1
  have hS : ∀ U ∈ η, U ≤ (S : Subgroup G) := fun U hU => (hη.1 hU).2
  have hle : ∀ t ∈ (S : Subgroup G), conjSub t (⨆ U ∈ η, U) ≤ ⨆ U ∈ η, U := by
    intro t ht
    rw [conjSub_iSup]
    refine iSup_le fun U => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hU => ?_
    exact le_iSup₂_of_le (conjSub t U) (hinv t ht U hU) le_rfl
  refine ⟨⨆ U ∈ η, U, ⟨η, ⟨S, hη, hinv⟩, rfl⟩, iSup₂_le hS, fun s hs => ?_⟩
  apply le_antisymm (hle s hs)
  have := conjSub_mono (n := s) (hle s⁻¹ ((S : Subgroup G).inv_mem hs))
  rwa [conjSub_conjSub_inv] at this

theorem E186Cent2.quot_odd {Ω : Set (Subgroup G)} (hΩ : HM MT Ω) {N : Subgroup G} [N.Normal]
    (hΩ' : HM MT (quotFamily Ω N))
    (hN : Odd (Nat.card N)) {K H : Subgroup G} (hK : K ∈ Ω) (h : E186Cent2 Ω K H) :
    E186Cent2 (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) (H.map (QuotientGroup.mk' N)) := by
  set mk := QuotientGroup.mk' N with hmk
  intro Lb hLb Jb hJb Rb₁ Rb₂ hRb₁ hRb₁L hRb₂ hRb₂J hc a ha ha1 ha2
  obtain ⟨L, hLtw, rfl⟩ := exists_lift_twin hΩ hN hK hLb
  have hLΩ : L ∈ Ω := hLtw.1
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hLΩ
  obtain ⟨R₁, hR₁, hR₁L, rfl⟩ := exists_lift_RSet hΩ' hN hLΩ hRb₁ hRb₁L
  have hR₁syl : IsSylow2In R₁ L := hΩ.isSylow2In_of_mem_RSet_of_le hLΩ hR₁ hR₁L
  have hR₁2 : IsPGroup 2 R₁ := hR₁syl.2.1
  have hR₁8 := hΩ.eight_le_of_mem_RSet hR₁
  have hJbΩ : Jb ∈ quotFamily Ω N := by
    rcases hJb with rfl | hJb'
    · exact map_mem_quotFamily hLΩ
    · exact hJb'.1
  obtain ⟨J₀, hJ₀, rfl⟩ := hJbΩ
  obtain ⟨R₂, hR₂, hR₂J, rfl⟩ := exists_lift_RSet hΩ' hN hJ₀ hRb₂ hRb₂J
  have hR₂syl : IsSylow2In R₂ J₀ := hΩ.isSylow2In_of_mem_RSet_of_le hJ₀ hR₂ hR₂J

  have final : ∀ (J R₂' : Subgroup G), J ∈ KPerp Ω L → R₂' ∈ RSet Ω → R₂' ≤ J →
      (Commutes R₁ R₂' ∨ R₂' = R₁) → R₂'.map mk = R₂.map mk → IsPGroup 2 ↥(R₁ ⊔ R₂') →
        Subgroup.centralizer ({a} : Set (G ⧸ N)) ≤ H.map mk := by
    intro J R₂' hJ hR₂' hR₂'J hcomm hmap hP
    have haP : a ∈ (R₁ ⊔ R₂').map mk := by
      rw [Subgroup.map_sup, hmap]
      exact ha
    obtain ⟨b, hbP, hb1, hb2, rfl⟩ := exists_involution_lift_of_isPGroup hN hP haP ha1 ha2
    exact (centralizer_map_le hN hb2).trans
      (Subgroup.map_mono (h L hLtw J hJ R₁ R₂' hR₁ hR₁L hR₂' hR₂'J hcomm b hbP hb1 hb2))
  rcases hc with hcomm | heq
  ·
    have hperm : ∀ x ∈ R₁, ∃ n ∈ N, conjSub x R₂ = conjSub n R₂ := by
      intro x hx
      have hxb : conjSub (mk x) (R₂.map mk) = R₂.map mk :=
        conjSub_eq_of_mem_of_commutes (Subgroup.mem_map_of_mem _ hx) hcomm
      have hmapx : (conjSub x R₂).map mk = R₂.map mk := by rw [AscQuot.map_conjSub, hxb]
      have hxle : conjSub x R₂ ≤ R₂ ⊔ N := by
        intro y hy
        have hy' : mk y ∈ R₂.map mk := hmapx ▸ Subgroup.mem_map_of_mem _ hy
        obtain ⟨r, hr, hry⟩ := hy'
        have hrn : r⁻¹ * y ∈ N := by
          have : QuotientGroup.mk' N (r⁻¹ * y) = 1 := by
            rw [map_mul, map_inv, hry, inv_mul_cancel]
          exact (QuotientGroup.eq_one_iff _).mp this
        have : y = r * (r⁻¹ * y) := by group
        rw [this]
        exact (R₂ ⊔ N).mul_mem (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right hrn)
      have hS₁ := isSylow2In_sup_of_odd hN hR₂syl.2.1
      have hS₂ : IsSylow2In (conjSub x R₂) (R₂ ⊔ N) :=
        hS₁.of_natCard_le (hR₂syl.2.1.map _) hxle (by
          rw [Nat.card_congr (Subgroup.equivMapOfInjective R₂ (MulAut.conj x).toMonoidHom
            (MulAut.conj x).injective).toEquiv]
          rfl)
      obtain ⟨p', hp', hpx⟩ := exists_conjSub_eq_of_isSylow2In hS₁ hS₂
      obtain ⟨r, hr, n, hn, hrn⟩ := Subgroup.mem_sup_of_normal_right.mp hp'
      refine ⟨r * n * r⁻¹, ‹N.Normal›.conj_mem n hn r, ?_⟩
      rw [← hpx, ← hrn]
      calc conjSub (r * n) R₂ = conjSub ((r * n * r⁻¹) * r) R₂ := by congr 1; group
        _ = conjSub (r * n * r⁻¹) (conjSub r R₂) := conjSub_mul _ _ _
        _ = conjSub (r * n * r⁻¹) R₂ := by rw [conjSub_eq_self_of_mem hr]
    obtain ⟨m, hm, hmN⟩ := exists_conj_normalizer_of_perm hN R₂ hR₁2 hperm
    have hmk1 : mk m = 1 := (QuotientGroup.eq_one_iff _).mpr hm
    have hJ'Ω : conjSub m J₀ ∈ Ω := hΩ.conjInvariant m J₀ hJ₀
    have hR₂'mem : conjSub m R₂ ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR₂ m
    have hR₂'J' : conjSub m R₂ ≤ conjSub m J₀ := conjSub_mono hR₂J
    have hmap : (conjSub m R₂).map mk = R₂.map mk := by
      rw [AscQuot.map_conjSub, hmk1, conjSub_one]
    have hR₂'syl : IsSylow2In (conjSub m R₂) (conjSub m J₀) :=
      hΩ.isSylow2In_of_mem_RSet_of_le hJ'Ω hR₂'mem hR₂'J'
    have hP : IsPGroup 2 ↥(R₁ ⊔ conjSub m R₂) := hR₁2.to_sup_of_normal_right' hR₂'syl.2.1 hmN
    by_cases hJL : conjSub m J₀ = L
    ·
      have hle : R₁ ⊔ conjSub m R₂ ≤ L := sup_le hR₁L (hJL ▸ hR₂'J')
      have hsyl : IsSylow2In (conjSub m R₂) L := hJL ▸ hR₂'syl
      have h1 : R₁ ⊔ conjSub m R₂ = conjSub m R₂ := hsyl.2.2 _ hle hP le_sup_right
      have h2 : R₁ ≤ conjSub m R₂ := h1 ▸ le_sup_left
      have heq' : conjSub m R₂ = R₁ :=
        (Subgroup.eq_of_le_of_card_ge h2 (hR₁syl.natCard_eq hsyl).ge).symm
      exact final L R₁ (Set.mem_insert _ _) hR₁ hR₁L (Or.inr rfl) (by rw [← heq', hmap])
        (by rw [sup_idem]; exact hR₁2)
    · have hLJ : L ≠ conjSub m J₀ := fun h' => hJL h'.symm
      have hne : R₁ ≠ conjSub m R₂ := by
        intro h'
        exact hLJ (hΩ.eq_of_le_of_le hLΩ hJ'Ω hR₁2 (by omega) hR₁L (h' ▸ hR₂'J'))
      obtain ⟨S, hS⟩ := hP.exists_le_sylow
      have hcomm' : Commutes R₁ (conjSub m R₂) :=
        l6_7_proved G Ω hΩ S R₁ hR₁ _ hR₂'mem (le_sup_left.trans hS)
          (le_sup_right.trans hS) hne
      have hzR₁ : z ∈ R₁ := AscL62.mem_of_uniqueInvolution_of_pGroup hz hR₁L hR₁2 (by omega)
      have hAc : conjSub m R₂ ≤ Subgroup.centralizer ({z} : Set G) := fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hcomm' z hzR₁ y hy).symm
      have hR₂'8 := hΩ.eight_le_of_mem_RSet hR₂'mem
      have hN' : conjSub m R₂ ≤ Subgroup.normalizer (L : Set G) :=
        hΩ.le_normalizer_of_le_centralizer hLΩ hJ'Ω hLJ hz hR₂'J' hR₂'syl.2.1 (by omega) hAc
      exact final (conjSub m J₀) (conjSub m R₂)
        (Set.mem_insert_of_mem _ ⟨hJ'Ω, hJL, conjSub m R₂, hR₂'mem, hR₂'J', hN'⟩) hR₂'mem hR₂'J'
        (Or.inl hcomm') hmap hP
  ·
    exact final L R₁ (Set.mem_insert _ _) hR₁ hR₁L (Or.inr rfl) heq.symm
      (by rw [sup_idem]; exact hR₁2)

variable {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.odd_quot_trans (c : MinCex MT Ω K S R W H) {N : Subgroup G} [N.Normal]
    (hΩ' : HM MT (quotFamily Ω N)) (hN : Odd (Nat.card N)) :
    ∀ Jb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N)),
      ∃ hb ∈ H.map (QuotientGroup.mk' N),
        conjSub hb (K.map (QuotientGroup.mk' N)) = Jb := by
  have hΩ : HM MT Ω := c.stand.hyp
  exact E187C.odd_quot_trans_of hΩ.conjInvariant
    (fun hL hL' hadj => exists_conj_omegaStarNbr hΩ hΩ' hN hL hL' hadj) c.hyp.trans c.stand.mem

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

section EndNone
variable [Finite G]

theorem endgame_none (hΩ : HypOmega MT Ω)
    (hodd : ∀ K ∈ Ω, Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K) {H : Subgroup G}
        {t : G}
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {d₁ d₂ : G}
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) (m₁ : conjSub d₁ K₁ ≠ K₁) (m₂ : conjSub d₂ K₁ ≠ K₁)
    (m₃ : conjSub (d₁ * d₂) K₁ ≠ K₁) : False := by
  exact E187C.endgame_none_of hΩ.toMod.conjInvariant
    (fun hM h => CFSG.ClassicalInvolution.Q3.Q3T7M.le_of_sq_mem_of_oddGen (hodd _ hM) h)
    (fun hM => hΩ.toMod.exists_orderOf_four_of_mem hM)
    (fun hK hJ hKJ hzK hzJ => hΩ.commutes_of_twin hK hJ hKJ hzK hzJ)
    hbad hK₁ ht g₁ g₂ g₃ hc m₁ m₂ m₃

end EndNone
end Asc77
end
end CFSG.ClassicalInvolution.T7FU
