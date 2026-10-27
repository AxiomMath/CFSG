module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoSt0A
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoSt0C
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoSt0B
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

variable {G : Type} [Group G] [Finite G] {J L L₀ : Subgroup G}

theorem inf_center_eq_bot (hc : F2CoreConfig J L L₀) {K : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) :
    K ⊓ Subgroup.center G = ⊥ := by
  obtain ⟨h, -, -, -, -, -, -, -, -, hZ, -, -⟩ := id hc
  obtain ⟨⟨z, hz⟩, -⟩ := h.hyp.omega1 K hK
  have hzZ := not_mem_center hc hK hz
  have h2 : IsPGroup 2 ↥(K ⊓ Subgroup.center G) := by
    have hP : IsPGroup 2 ↥(Subgroup.center G) := by
      rw [← hZ]
      exact CFSG.pCore_isPGroup
    exact hP.to_le inf_le_right
  by_contra hne
  have hnt : Nontrivial ↥(K ⊓ Subgroup.center G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨a, ha⟩ := h2.exists_card_eq
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero] at ha
    exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' ha
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [ha]; exact dvd_pow_self 2 ha0)
  have hy2 : (y : G) * y = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy, pow_two] at this
    exact congrArg Subtype.val this
  have hy1 : (y : G) ≠ 1 := by
    intro h1
    have : y = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hy
    exact absurd hy (by norm_num)
  rcases hz.unique y (Subgroup.mem_inf.mp y.2).1 hy2 with h1 | h1
  · exact hy1 h1
  · exact hzZ (h1 ▸ (Subgroup.mem_inf.mp y.2).2)

theorem nonempty_equiv_of_isSylow2In {X Q : Type} [Group X] [Finite X] [Group Q]
    {M P P₀ : Subgroup X} (hP : IsSylow2In P M) (hP₀ : IsSylow2In P₀ M) (e : ↥P₀ ≃* Q) :
    Nonempty (↥P ≃* Q) := by
  obtain ⟨x, -, hx⟩ := Thompson.exists_conj_of_isSylow2In hP₀ hP
  subst hx
  exact ⟨(P₀.equivMapOfInjective (MulAut.conj x).toMonoidHom
    (MulAut.conj x).injective).symm.trans e⟩

theorem false_of_socle {P : ∀ (F : Type) [Group F], Prop}
    (hPinv : ∀ {A B : Type} [Group A] [Group B], (A ≃* B) → P A → P B)
    (hT : SocleTransitive P) (hc : F2CoreConfig J L L₀)
    (hP : P (↥L₀ ⧸ Subgroup.center ↥L₀)) : False := by
  obtain ⟨h, hnc, -, -, -, hL₀, hn, -, -, hZ, hC, hmem⟩ := id hc
  set Z : Subgroup G := Subgroup.center G with hZdef
  set Δ := CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L with hΔ
  have hmeet : ∀ K ∈ Δ, K ⊓ Z = ⊥ := fun K hK => inf_center_eq_bot hc hK
  have hq8 : ∀ K ∈ Δ, ∃ P : Subgroup G, IsSylow2In P K ∧ Nonempty (↥P ≃* QuaternionGroup 2) := by
    intro K hK
    obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := K) IsPGroup.of_bot bot_le
    exact ⟨P, hP, h.quat K hK P hP⟩
  have hcq := centQuotGen h.hyp hq8 le_rfl hmeet
  set Δb := quotFamily Δ Z with hΔb
  have hZ2 : IsPGroup 2 ↥Z := hZ ▸ CFSG.pCore_isPGroup
  have hoddb : classicalInvolutionOddCore (G ⧸ Z) = ⊥ := by
    rw [eq_bot_iff]
    intro xb hxb
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z xb
    have hker : (QuotientGroup.mk' Z).ker = Z := QuotientGroup.ker_mk' Z
    have h1 := TwistQ.comap_oddCore_le (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
      (by rw [hker]) (by rw [hker]; exact hZ2) (Subgroup.mem_comap.mpr hxb)
    rw [h.odd, bot_sup_eq, hker] at h1
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h1
  have hTb : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 (G ⧸ Z) Δb :=
    { hyp := hcq.hyp'
      twoGroup := two_quot_cent h.twoGroup hmeet
      quat := by
        intro M hM P hP
        obtain ⟨P₀, hP₀, ⟨e⟩⟩ := q8_quot_cent hq8 hmeet M hM
        exact nonempty_equiv_of_isSylow2In hP hP₀ e
      aEmpty := hcq.aEmpty_quotFamily h.aEmpty
      odd := hoddb }
  set Nb : Subgroup (G ⧸ Z) := L₀.map (QuotientGroup.mk' Z) with hNbdef
  have hNbn : Nb.Normal := hn.map _ (QuotientGroup.mk'_surjective Z)
  have hNbs : IsSimpleGroup ↥Nb := isSimpleGroup_bar hL₀.1 le_rfl hC
  have hnab := exists_ne_comm_bar hL₀.1 le_rfl hC
  have hCb := centralizer_bar_eq_bot hL₀.1 le_rfl hC
  have hPb : P ↥Nb := hPinv (barEquiv le_rfl hC).symm hP
  have hmemb : ∀ M ∈ Δb, ∀ zb : G ⧸ Z, IsUniqueInvolution M zb → zb ∈ Nb := by
    rintro _ ⟨K, hK, rfl⟩ zb hzb
    obtain ⟨⟨z, hz⟩, -⟩ := h.hyp.omega1 K hK
    have hz' := AscQuot.isUniqueInvolution_map_mk (hmeet K hK) hz
    rw [← hz'.eq hzb]
    exact Subgroup.mem_map_of_mem _ (hmem K hK z hz)
  have hJ : J ∈ Δ := Or.inl (CoreAssembly.mem_conjClass_self J)
  have hL : L ∈ Δ := Or.inr (CoreAssembly.mem_conjClass_self L)
  obtain ⟨gb, hg⟩ := hT (G ⧸ Z) Nb hnab hCb hPb Δb hTb hmemb _ (map_mem_quotFamily hJ) _
    (map_mem_quotFamily hL)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z gb
  have hgJ : conjSub g J ∈ Δ := h.hyp.conjInvariant g J hJ
  refine hnc ⟨g, hcq.eq_of_map _ hgJ _ hL ?_⟩
  rw [AscQuot.map_conjSub]
  exact hg

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
