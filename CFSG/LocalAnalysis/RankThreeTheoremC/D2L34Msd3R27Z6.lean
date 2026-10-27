module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27AutL34
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27LemmaP
import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerBalance
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.L34Exp3
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Basic
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.EscapeCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore primeComplementCore_coprime)
open CFSG.PreuniquenessRankFour.Helpers (fullCore_le_iff pRank_attained
  elementary_abelian_sup_of_commuting elementary_subgroup_eq_of_rank_bound)
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim (normalizer_map_le_map_normalizer)

variable {G : Type} [Group G] [Finite G] {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
  {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

private theorem commute_conj_of_pow_three {X : Type*} [Group X] {x y : X} (hx : x ^ 3 = 1)
    (h₁ : (y * x⁻¹) ^ 3 = 1) (h₂ : (x * y) ^ 3 = 1) :
    y * (x⁻¹ * y * x) = x⁻¹ * y * x * y := by
  have e₁ : y * x⁻¹ * y = x * y⁻¹ * x := by
    have h : y * x⁻¹ * y * x⁻¹ * y * x⁻¹ = 1 := by
      rw [← h₁]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    calc y * x⁻¹ * y = y * x⁻¹ * y * x⁻¹ * y * x⁻¹ * (x * y⁻¹ * x) := by group
      _ = x * y⁻¹ * x := by rw [h, one_mul]
  have e₂ : y * x * y = x⁻¹ * y⁻¹ * x⁻¹ := by
    have h : x * y * x * y * x * y = 1 := by
      rw [← h₂]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    calc y * x * y = x⁻¹ * (x * y * x * y * x * y) * y⁻¹ * x⁻¹ := by group
      _ = x⁻¹ * y⁻¹ * x⁻¹ := by rw [h, mul_one]
  have e₃ : x * x = x⁻¹ := by
    have h : x * x * x = 1 := by
      rw [← hx]
      simp only [pow_succ, pow_zero, one_mul]
    exact eq_inv_of_mul_eq_one_left h
  have e₄ : x⁻¹ * x⁻¹ = x := by rw [← mul_inv_rev, e₃, inv_inv]
  calc y * (x⁻¹ * y * x) = y * x⁻¹ * y * x := by group
    _ = x * y⁻¹ * x * x := by rw [e₁]
    _ = x * y⁻¹ * x⁻¹ := by rw [mul_assoc (x * y⁻¹) x x, e₃]
    _ = x⁻¹ * x⁻¹ * y⁻¹ * x⁻¹ := by rw [e₄]
    _ = x⁻¹ * (x⁻¹ * y⁻¹ * x⁻¹) := by group
    _ = x⁻¹ * y * x * y := by rw [← e₂]; group

private theorem normalizer_zpowers_conj_le {X : Type*} [Group X] {X₀ : Subgroup X} {s u : X}
    (hu : u ∈ X₀) (hs : Subgroup.normalizer (Subgroup.zpowers s : Set X) ≤ X₀) :
    Subgroup.normalizer (Subgroup.zpowers (u⁻¹ * s * u) : Set X) ≤ X₀ := by
  have hmap : (Subgroup.zpowers s).map (MulAut.conj u⁻¹).toMonoidHom =
      Subgroup.zpowers (u⁻¹ * s * u) := by
    rw [MonoidHom.map_zpowers]
    simp [MulAut.conj_apply]
  rw [← hmap, ← Subgroup.map_equiv_normalizer_eq]
  rintro _ ⟨x, hx, rfl⟩
  have hxX₀ := hs hx
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
  exact X₀.mul_mem (X₀.mul_mem (X₀.inv_mem hu) hxX₀) hu

private theorem exists_pow_lift_orderOf_three {Y : Type*} [Group Y] [Finite Y] (O : Subgroup Y)
    [O.Normal] (hO : Nat.Coprime 3 (Nat.card O)) (y : Y)
    (hy : orderOf (QuotientGroup.mk' O y) = 3) :
    ∃ m : ℕ, QuotientGroup.mk' O (y ^ m) = QuotientGroup.mk' O y ∧ orderOf (y ^ m) = 3 := by
  have hN : ¬ 3 ∣ Nat.card O := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hO
  have hdvd : 3 ∣ orderOf y := hy ▸ orderOf_map_dvd (QuotientGroup.mk' O) y
  obtain ⟨s, hs⟩ := hdvd
  have hypN : y ^ 3 ∈ O := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    have := pow_orderOf_eq_one (QuotientGroup.mk' O y)
    rwa [hy] at this
  have hord : orderOf (y ^ 3) = s := by
    rw [orderOf_pow_of_dvd (by norm_num) ⟨s, hs⟩, hs, Nat.mul_div_cancel_left _ (by norm_num)]
  have hsN : s ∣ Nat.card O := by
    rw [← hord]
    have := orderOf_dvd_natCard (⟨y ^ 3, hypN⟩ : O)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime s 3 :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      fun h => hN (h.trans hsN))
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num : 1 < 3)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact (orderOf_pos y).ne' (by simpa using hs)
  have hmod : t * s ≡ 1 [MOD 3] := by
    unfold Nat.ModEq
    rw [mul_comm, ht]
  have htp : Nat.Coprime 3 t := (Nat.coprime_of_mul_modEq_one s hmod).symm
  have hq : t * s = 3 * (s * t / 3) + 1 := by
    have := Nat.div_add_mod (s * t) 3
    rw [ht] at this
    linarith [mul_comm t s]
  refine ⟨t * s, ?_, ?_⟩
  · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hq, pow_succ,
      pow_mul]
    have e : (((y ^ 3) ^ (s * t / 3)) * y)⁻¹ * y = ((y ^ 3) ^ (s * t / 3))⁻¹ := by group
    rw [e]
    exact O.inv_mem (O.pow_mem hypN _)
  · rw [orderOf_pow, hs, Nat.gcd_mul_right, htp, one_mul,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs0)]

private theorem not_normalizer_zpowers_le_of_outer
    {X : Type} [Group X] [Finite X] {Rb : Sylow 3 X}
    {Ab X₀ L : Subgroup X} (hK : D2AlmostSimple 3 X Rb Ab X₀ L) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsL34Index d) (he : Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)) (hAK : Ab ≤ L)
    {s : X} (hsA : s ∈ Subgroup.normalizer (Ab : Set X)) (hsX₀ : s ∈ X₀) (hsK : s ∉ L)
    (hs3 : s ^ 3 = 1) : ¬ Subgroup.normalizer (Subgroup.zpowers s : Set X) ≤ X₀ := by
  intro hN
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAX₀ : Ab ≤ X₀ := hK.A_le.trans hK.sylow_le
  have hrk : ∀ Y : Subgroup X, Open.pRank 3 Y ≤ 2 := fun Y =>
    (pRank_le_pRank_sylow Nat.prime_three Rb Y).trans hK.pRank_eq.le
  have hsel : IsElemAbelian 3 (Subgroup.zpowers s) := CFSG.Open.isElemAbelian_zpowers hs3
  have hsp : IsPGroup 3 (Subgroup.zpowers s) := hsel.isPGroup
  have hBp : IsPGroup 3 (Subgroup.zpowers s ⊔ Ab : Subgroup X) :=
    IsPGroup.to_sup_of_normal_right' hsp hK.elem.isPGroup (Subgroup.zpowers_le.mpr hsA)
  have hBexp : ∀ x ∈ (Subgroup.zpowers s ⊔ Ab : Subgroup X), x ^ 3 = 1 := fun x hx =>
    Tits.S3AmalgamBound.kFactL34Exp3 d hd X L hK.normal hK.centralizer_eq_bot he x
      (hBp.to_le (Subgroup.zpowers_le.mpr hx))
  have hsB : s ∈ (Subgroup.zpowers s ⊔ Ab : Subgroup X) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers s)
  have hsord : orderOf s = 3 := orderOf_eq_prime hs3 fun h => hsK (h ▸ L.one_mem)
  obtain ⟨a, haA, has⟩ : ∃ a ∈ Ab, a * s ≠ s * a := by
    by_contra hcon'
    have hcon : ∀ a ∈ Ab, a * s = s * a := fun a ha => by
      by_contra h
      exact hcon' ⟨a, ha, h⟩
    have hAC : Ab ≤ Subgroup.centralizer (Subgroup.zpowers s : Set X) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (show Commute s a from (hcon a ha).symm) k).eq
    have heq := elementary_subgroup_eq_of_rank_bound 3 Nat.prime_three
      (elementary_abelian_sup_of_commuting 3 hK.elem hsel hAC)
      le_sup_left 2 hK.card_A (hrk _)
    have hsAb : s ∈ Ab := by
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
    exact hsK (hAK hsAb)
  have haB : a ∈ (Subgroup.zpowers s ⊔ Ab : Subgroup X) := Subgroup.mem_sup_right haA
  obtain ⟨c, hc⟩ : ∃ c : X, c = a⁻¹ * s * a * s⁻¹ := ⟨_, rfl⟩
  have hcA : c ∈ Ab := by
    have hsa : s * a * s⁻¹ ∈ Ab := (Subgroup.mem_normalizer_iff.mp hsA a).mp haA
    have e : c = a⁻¹ * (s * a * s⁻¹) := by rw [hc]; group
    rw [e]
    exact Ab.mul_mem (Ab.inv_mem haA) hsa
  have hcs' : a⁻¹ * s * a = c * s := by rw [hc]; group
  have hc1 : c ≠ 1 := by
    intro h1
    apply has
    rw [h1, one_mul] at hcs'
    calc a * s = a * (a⁻¹ * s * a) := by rw [hcs']
      _ = s * a := by group
  have hu := commute_conj_of_pow_three (hK.elem.2 a haA)
    (hBexp _ ((Subgroup.zpowers s ⊔ Ab).mul_mem hsB ((Subgroup.zpowers s ⊔ Ab).inv_mem haB)))
    (hBexp _ ((Subgroup.zpowers s ⊔ Ab).mul_mem haB hsB))
  have hcs : Commute c s := by
    show c * s = s * c
    calc c * s = a⁻¹ * s * a := hcs'.symm
      _ = a⁻¹ * s * a * s * s⁻¹ := by group
      _ = s * (a⁻¹ * s * a) * s⁻¹ := by rw [hu]
      _ = s * c := by rw [hcs']; group
  have hca : Commute c a := by
    have := hK.elem.1.is_comm.comm ⟨c, hcA⟩ ⟨a, haA⟩
    exact congrArg Subtype.val this
  have hconj : ∀ n : ℕ, (a ^ n)⁻¹ * s * a ^ n = c ^ n * s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcn : a⁻¹ * c ^ n = c ^ n * a⁻¹ := ((hca.pow_left n).inv_right).eq.symm
      calc (a ^ (n + 1))⁻¹ * s * a ^ (n + 1) = a⁻¹ * ((a ^ n)⁻¹ * s * a ^ n) * a := by
            rw [pow_succ]; group
        _ = (a⁻¹ * c ^ n) * s * a := by rw [ih]; group
        _ = c ^ n * (a⁻¹ * s * a) := by rw [hcn]; group
        _ = c ^ (n + 1) * s := by rw [hcs', pow_succ]; group
  have hc3 : c ^ 3 = 1 := hK.elem.2 c hcA
  have hcC : Subgroup.zpowers c ≤ Subgroup.centralizer (Subgroup.zpowers s : Set X) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left hcs.symm k).eq
  set E : Subgroup X := Subgroup.zpowers c ⊔ Subgroup.zpowers s with hE
  have hEel : IsElemAbelian 3 E :=
    elementary_abelian_sup_of_commuting 3 (CFSG.Open.isElemAbelian_zpowers hc3) hsel hcC
  have hsE : s ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  have hcAb : Subgroup.zpowers c ≤ Ab := Subgroup.zpowers_le.mpr hcA
  have hsc : s ∉ Subgroup.zpowers c := fun h => hsK (hAK (hcAb h))
  have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hE9 : Nat.card E = 3 ^ 2 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEel.isPGroup
    have hk2 : k ≤ 2 := (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hEel hk).trans (hrk E)
    have hk2' : 2 ≤ k := by
      by_contra hlt
      have hle : Nat.card E ≤ Nat.card (Subgroup.zpowers c) := by
        rw [hk, Nat.card_zpowers, hcord]
        calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 3 := by norm_num
      have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : Subgroup.zpowers c ≤ E) hle
      exact hsc (heq ▸ hsE)
    rw [hk, show k = 2 by omega]
  have htop := kFactL34Outer d hd X L hK.normal hK.centralizer_eq_bot he E hEel hE9
    fun h => hsK (h hsE)
  have hEX₀ : E ≤ X₀ := sup_le (hcAb.trans hAX₀) (Subgroup.zpowers_le.mpr hsX₀)
  apply hK.ne_top
  rw [eq_top_iff, ← htop]
  refine (fullCore_le_iff 3 1 E X₀).mpr fun Q hQE hQr => ?_
  by_cases hQ2 : 2 ≤ Open.pRank 3 Q
  · exact hK.normalizer_le_of_rank Q (hQE.trans hEX₀) (hEel.isPGroup.to_le hQE) hQ2
  have hQne : Q ≠ ⊥ := by
    intro hQ
    obtain ⟨F, hF, -, hFcard⟩ := pRank_attained 3 Nat.prime_three Q
    rw [hQ, le_bot_iff] at hF
    rw [hF, Subgroup.card_bot] at hFcard
    have := Nat.one_lt_pow (by omega : Open.pRank 3 Q ≠ 0) (by norm_num : 1 < 3)
    omega
  by_cases hQc : Q ≤ Subgroup.zpowers c
  · exact hK.normalizer_le_of_le_A Q (hQc.trans hcAb) hQne
  obtain ⟨g, hgQ, hgc⟩ := Set.not_subset.mp hQc
  have hgE : g ∈ E := hQE hgQ
  rw [← SetLike.mem_coe, hE, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (hcC.trans (Subgroup.centralizer_le_normalizer _)), Set.mem_mul] at hgE
  obtain ⟨u, hu', v, hv', rfl⟩ := hgE
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, c ^ i = u := by
    obtain ⟨i, hi⟩ := (mem_powers_iff_mem_zpowers.mpr hu' : u ∈ Submonoid.powers c)
    exact ⟨i, hi⟩
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, s ^ j = v := by
    obtain ⟨j, hj⟩ := (mem_powers_iff_mem_zpowers.mpr hv' : v ∈ Submonoid.powers s)
    exact ⟨j, hj⟩
  obtain ⟨k, hkQ⟩ : ∃ k : ℕ, c ^ k * s ∈ Q := by
    have hj3 : s ^ j = s ^ (j % 3) := by
      rw [← hsord, pow_mod_orderOf]
    have hjlt : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hj : j % 3
    · exfalso
      apply hgc
      rw [hj3, pow_zero, mul_one]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) i
    · exact ⟨i, by rw [hj3, pow_one] at hgQ; exact hgQ⟩
    · refine ⟨2 * i, ?_⟩
      have hsq : (c ^ i * s ^ j) ^ 2 = c ^ (2 * i) * s := by
        rw [hj3, (hcs.pow_pow i 2).mul_pow, ← pow_mul, ← pow_mul, mul_comm i 2]
        congr 1
        rw [show 2 * 2 = 3 + 1 by norm_num, pow_succ, hs3, one_mul]
      rw [← hsq]
      exact Q.pow_mem hgQ 2
  have ht1 : c ^ k * s ≠ 1 := by
    intro h1
    apply hsc
    have : s = (c ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) k)
  have htord : orderOf (c ^ k * s) = 3 :=
    orderOf_eq_prime (hEel.2 _ (hQE hkQ)) ht1
  have hQel : IsElemAbelian 3 Q := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => hEel.2 x (hQE hx)⟩
    have h := hEel.1.is_comm.comm (⟨x, hQE x.2⟩ : E) ⟨y, hQE y.2⟩
    show (x : X) * y = y * x
    exact congrArg Subtype.val h
  have hQt : Subgroup.zpowers (c ^ k * s) = Q := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQel.isPGroup
    have hm1 : m ≤ 1 := by
      have := CFSG.SectionRank.le_pRank (by norm_num) le_rfl hQel hm
      omega
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hkQ) ?_
    rw [hm, Nat.card_zpowers, htord]
    calc 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm1
      _ = 3 := by norm_num
  rw [← hQt, ← hconj k]
  exact normalizer_zpowers_conj_le (X₀.pow_mem (hAX₀ haA) k) hN

theorem D2L34SideCtx3.index_eq_six_or_twelve
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K)
    (h27 : Nat.card R = 27) : K.index = 6 ∨ K.index = 12 := by
  have hc := ctx.conf
  have hRR : Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) = Nat.card R := by
    rw [hc.rbar]
    exact hc.esc.card_map_eq le_rfl
  exact l34_index_eq_six_or_twelve hc.l34 hc.almostSimple.normal
    hc.almostSimple.centralizer_eq_bot hc.iso hc.almostSimple.elem hc.almostSimple.card_A hc.le_K
    hc.not_centralizer_le (h27 ▸ hRR ▸ Subgroup.card_subgroup_dvd_card _)

theorem D2L34SideCtx3.exists_order_three_of_index_six
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K) (h27 : Nat.card R = 27) (h6 : K.index = 6)
    {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    ∃ h ∈ H ⊓ M, h ∈ Subgroup.normalizer (T : Set G) ∧ orderOf h = 3 ∧
      ¬ Subgroup.normalizer (Subgroup.zpowers h : Set G) ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := ctx.conf
  set O := primeComplementCore (G := H) 3 with hO
  set π := QuotientGroup.mk' O with hπ
  have hOM : O ≤ (H ⊓ M).subgroupOf H := by
    rw [hO, ← glbPrimeCore_subgroupOf]
    exact glbPrimeCore_subgroupOf_le_inf hc.esc.primeCore_le
  have hX₀N : ((H ⊓ M).subgroupOf H).map π =
      Subgroup.normalizer (((A.subgroupOf H).map π : Subgroup _) : Set _) :=
    hc.almostSimple.eq_normalizer_of_l34 kFactL34Inner hc.l34 hc.iso hc.le_K
  obtain ⟨s, hsA, hsT, hsK, hs3⟩ := l34_exists_outer_three_normalizing hc.l34
    hc.almostSimple.normal hc.almostSimple.centralizer_eq_bot hc.iso hc.almostSimple.elem
    hc.almostSimple.card_A hc.le_K hc.not_centralizer_le h6 (hc.isSylowTwoOf_map hT)
  have hsX₀ : s ∈ ((H ⊓ M).subgroupOf H).map π := by
    rw [hX₀N]
    exact hsA
  have hsord : orderOf s = 3 := orderOf_eq_prime hs3 fun h => hsK (h ▸ K.one_mem)
  obtain ⟨y, hyN, hys⟩ := normalizer_map_le_map_normalizer hc.esc.primeCore_le hT hsT
  obtain ⟨m, hm, hm3⟩ := exists_pow_lift_orderOf_three O (primeComplementCore_coprime 3) y
    (by rw [hys]; exact hsord)
  have hhs : π (y ^ m) = s := hm.trans hys
  have hhHM : y ^ m ∈ (H ⊓ M).subgroupOf H := by
    have hmem : y ^ m ∈ (((H ⊓ M).subgroupOf H).map π).comap π := by
      show π (y ^ m) ∈ ((H ⊓ M).subgroupOf H).map π
      rw [hhs]
      exact hsX₀
    rwa [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk', sup_eq_left.mpr hOM] at hmem
  refine ⟨((y ^ m : H) : G), Subgroup.mem_subgroupOf.mp hhHM, ?_, ?_, ?_⟩
  · have hyT : (y : G) ∈ Subgroup.normalizer (T : Set G) := (Subgroup.mem_subgroupOf.mp hyN).2
    rw [Subgroup.coe_pow]
    exact Subgroup.pow_mem _ hyT m
  · rw [Subgroup.orderOf_coe, hm3]
  · intro hN
    have hQ : IsPGroup 3 (Subgroup.zpowers (y ^ m)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hm3, pow_one])
    have hmapG : (Subgroup.zpowers (y ^ m)).map H.subtype = Subgroup.zpowers ((y ^ m : H) : G) :=
      MonoidHom.map_zpowers _ _
    have hNX := normalizer_map_mk_le_map_inf Nat.prime_three O (primeComplementCore_coprime 3)
      hOM hQ (by rw [hmapG]; exact hN)
    rw [MonoidHom.map_zpowers, ← hπ, hhs] at hNX
    exact not_normalizer_zpowers_le_of_outer hc.almostSimple hc.l34 hc.iso hc.le_K hsA hsX₀ hsK
      hs3 hNX

theorem D2L34SideCtx3.noNonExtremal_of_index_six
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K) (h27 : Nat.card R = 27) (h6 : K.index = 6)
    {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) : D2NoNonExtremalAt P M T := by
  intro E N hesc hTN
  obtain ⟨h, hhHM, hhT, hh3, hhN⟩ := ctx.exists_order_three_of_index_six h27 h6 hT
  exact hhN (ctx.normalizer_zpowers_le_of_escape hesc (hTN hhT) hhHM.2 hh3)

end CFSG.LocalAnalysis.RankThreeTheoremC
