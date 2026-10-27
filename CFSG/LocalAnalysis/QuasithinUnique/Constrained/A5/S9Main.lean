module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9T
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9Aut3
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S7D
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9K
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32S

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.Id2519

namespace U9Data

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {z u : G} {A V K : Subgroup G}
  (D : U9Data T M H S L z u A V)

include D

omit [Finite G] in
theorem not_le_centralizer_v (hKq : CFSG.IsQuasisimple ↥K) {v : G}
    (hv : v ∈ blockU L ⊓ Subgroup.centralizer (A : Set G)) (hv1 : v ≠ 1) (hvu : v ≠ u) :
    ¬ K ≤ Subgroup.centralizer ({v} : Set G) := by
  intro hKv
  obtain ⟨l, -, hvl⟩ := D.s7.CU_conj v (by rw [← D.A_eq]; exact hv) hv1 hvu
  have hz : z = l * v * l⁻¹ := by rw [hvl]; group
  have hKM : ∀ k ∈ K, l * k * l⁻¹ ∈ M := by
    intro k hk
    apply D.mem_M_of_commute
    have hkv : k * v = v * k := Subgroup.mem_centralizer_singleton_iff.mp (hKv hk)
    rw [hz]
    calc l * v * l⁻¹ * (l * k * l⁻¹) = l * (v * k) * l⁻¹ := by group
      _ = l * (k * v) * l⁻¹ := by rw [hkv]
      _ = l * k * l⁻¹ * (l * v * l⁻¹) := by group
  have hsolM : Group.IsSolvable ↥M := D.s7.M_solvable
  let f : ↥K →* ↥M :=
    { toFun := fun k => ⟨l * (k : G) * l⁻¹, hKM k k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show l * ((a : G) * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹)
        group) }
  have hf : Function.Injective f := fun a b h => Subtype.ext (by
    have h1 : l * (a : G) * l⁻¹ = l * (b : G) * l⁻¹ := congrArg Subtype.val h
    exact mul_left_cancel (mul_right_cancel h1))
  have hsolK : Group.IsSolvable ↥K := Group.isSolvable_of_isSolvable_injective hf
  exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hKq hsolK

theorem exists_v : ∃ v ∈ blockU L ⊓ Subgroup.centralizer (A : Set G), v ≠ 1 ∧ v ≠ u := by
  by_contra hne
  push Not at hne
  have hle : (blockU L ⊓ Subgroup.centralizer (A : Set G)) ≤ Subgroup.zpowers u := by
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]
      exact one_mem _
    · rw [hne v hv hv1]
      exact Subgroup.mem_zpowers u
  have h4 : Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) = 4 := by
    have := D.s7.CU_card
    rwa [← D.A_eq] at this
  have h2 : Nat.card ↥(Subgroup.zpowers u) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((pow_two u).trans D.u_sq') D.u_ne_one
  have := Subgroup.card_le_of_le hle
  omega

omit [Finite G] in
theorem uz_ne_one : u * z ≠ 1 := by
  intro h
  apply D.u_ne_z
  have : u = z⁻¹ := by
    calc u = (u * z) * z⁻¹ := by group
      _ = z⁻¹ := by rw [h, one_mul]
  rw [this]
  exact inv_eq_of_mul_eq_one_right D.z_sq'

theorem V_le_K (hKnorm : centralizerElem u ≤ Subgroup.normalizer (K : Set G))
    (huzK : u * z ∈ K) : V ≤ K := by
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := fun a ha => hKnorm (D.A_le_Hu ha).2
  exact D.hA.le_of_mem hAN huzK D.uz_mem D.uz_ne_one

theorem A_le_K_of_A6 (hKnorm : centralizerElem u ≤ Subgroup.normalizer (K : Set G))
    (hK : K ≤ centralizerElem u) (huzK : u * z ∈ K)
    (hZK : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k = 1)
    (e₀ : ↥K ≃* alternatingGroup (Fin 6)) (hT2 : IsPGroup 2 ↥T) : A ≤ K := by
  have hVK := D.V_le_K hKnorm huzK
  obtain ⟨c, hcA, hc3, -, -, hAc⟩ := D.hA.exists_c
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hcG : c ∈ centralizerElem u := (D.A_le_Hu hcA).2
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hKnorm hcG
  obtain ⟨k₀, hk₀⟩ := aut_inner_of_pow_three e₀ (conjAutK c hcN) (fun k => by
    apply Subtype.ext
    show c⁻¹ * (c⁻¹ * (c⁻¹ * (k : G) * c) * c) * c = k
    calc c⁻¹ * (c⁻¹ * (c⁻¹ * (k : G) * c) * c) * c = (c ^ 3)⁻¹ * (k : G) * c ^ 3 := by
          rw [pow_three]; group
      _ = k := by rw [hc3']; simp)
  have hbC : ∀ a ∈ K, a * (c * (k₀ : G)) = (c * (k₀ : G)) * a := by
    intro a ha
    have h1 := congrArg Subtype.val (hk₀ ⟨a, ha⟩)
    have h2 : c⁻¹ * a * c = (k₀ : G) * a * (k₀ : G)⁻¹ := h1
    calc a * (c * (k₀ : G)) = c * (c⁻¹ * a * c) * (k₀ : G) := by group
      _ = c * ((k₀ : G) * a * (k₀ : G)⁻¹) * (k₀ : G) := by rw [h2]
      _ = (c * (k₀ : G)) * a := by group
  have hbG : c * (k₀ : G) ∈ centralizerElem u := Subgroup.mul_mem _ hcG (hK k₀.2)
  have hbCK : c * (k₀ : G) ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => hbC a ha
  have hbT : c * (k₀ : G) ∈ T := D.B_le_T huzK ⟨hbG, hbCK⟩
  obtain ⟨n, hn⟩ := hT2 ⟨c * (k₀ : G), hbT⟩
  have hn' : (c * (k₀ : G)) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hbk : (c * (k₀ : G)) * (k₀ : G)⁻¹ = c := by group
  have hcomm : Commute (c * (k₀ : G)) (k₀ : G)⁻¹ :=
    (Commute.inv_right (show Commute (c * (k₀ : G)) (k₀ : G) from
      (Subgroup.mem_centralizer_iff.mp hbCK (k₀ : G) k₀.2).symm))
  have hb3k : (c * (k₀ : G)) ^ 3 = (k₀ : G) ^ 3 := by
    have h1 : ((c * (k₀ : G)) * (k₀ : G)⁻¹) ^ 3 = 1 := by rw [hbk]; exact hc3'
    rw [hcomm.mul_pow, inv_pow] at h1
    exact mul_inv_eq_one.mp h1
  have hb3 : (c * (k₀ : G)) ^ 3 = 1 := by
    refine hZK _ (by rw [hb3k]; exact K.pow_mem k₀.2 3) (fun k' hk' => ?_)
    exact (Subgroup.mem_centralizer_iff.mp ((Subgroup.centralizer (K : Set G)).pow_mem hbCK 3) k'
      hk').symm
  have hb1 : c * (k₀ : G) = 1 := by
    have h1 : orderOf (c * (k₀ : G)) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
    have h2 : orderOf (c * (k₀ : G)) ∣ 3 := orderOf_dvd_of_pow_eq_one hb3
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left n (by norm_num)) h1 h2)
  have hcK : c ∈ K := by
    have : c = (k₀ : G)⁻¹ := eq_inv_of_mul_eq_one_left hb1
    rw [this]
    exact K.inv_mem k₀.2
  rw [hAc]
  exact sup_le hVK (Subgroup.zpowers_le.mpr hcK)

theorem B_le_R (huzK : u * z ∈ K) (hVK : V ≤ K) :
    centralizerElem u ⊓ Subgroup.centralizer (K : Set G) ≤ baum S := by
  intro b hb
  have hbT : b ∈ T := D.B_le_T huzK hb
  exact D.mem_R_of_centralizes hbT hb.1 fun v hv =>
    (Subgroup.mem_centralizer_iff.mp hb.2 v (hVK hv)).symm

theorem RK_sylow (hAK : A ≤ K)
    (hTu : T ⊓ centralizerElem u ≤ Subgroup.normalizer (K : Set G)) (hT2 : IsPGroup 2 ↥T)
    (hST : S ≤ T) (hcard : Nat.card ↥K = 360) : IsSylowTwoOf (baum S ⊓ K) K := by
  obtain ⟨x, hxT, hxS, hxu⟩ := D.s7.x_exists
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hTu ⟨hxT, hxu⟩
  have hR := D.R_eq x hxT hxS
  have hVP : V ≤ baum S ⊓ K := le_inf (D.V_le.trans D.U_le_R) (D.V_le_A.trans hAK)
  have hVxU : conjR V x ≤ conjR (blockU L) x := Subgroup.map_mono D.V_le
  have hVxP : conjR V x ≤ baum S ⊓ K := by
    refine le_inf ?_ ?_
    · rw [hR]
      exact hVxU.trans le_sup_right
    · intro y hy
      rw [mem_conjR_iff] at hy
      have hyK : x * y * x⁻¹ ∈ K := hAK (D.V_le_A hy)
      have hxi : x⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
        (Subgroup.normalizer (K : Set G)).inv_mem hxN
      have := (Subgroup.mem_normalizer_iff.mp hxi (x * y * x⁻¹)).mp hyK
      simpa [mul_assoc] using this
  have hVcard : Nat.card V = 4 := D.hA.card_U
  have hVxcard : Nat.card ↥(conjR V x) = 4 := by
    unfold conjR
    rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective]
    exact hVcard
  have hne : V ≠ conjR V x := by
    intro h
    exact D.not_le_conj hxT hxS (h ▸ hVxU)
  have hP2 : IsPGroup 2 ↥(baum S ⊓ K) := by
    refine hT2.to_le ?_
    exact inf_le_left.trans ((baum_le_S).trans hST)
  obtain ⟨n, hn⟩ := hP2.exists_card_eq
  have hdvd4 : 4 ∣ 2 ^ n := by
    rw [← hn, ← hVcard]
    exact Subgroup.card_dvd_of_le hVP
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    interval_cases n <;> simp at hdvd4
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have hn2' : n = 2 := by omega
    subst hn2'
    apply hne
    have h1 : V = baum S ⊓ K :=
      Subgroup.eq_of_le_of_card_ge hVP (by rw [hn, hVcard]; norm_num)
    have h2 : conjR V x = baum S ⊓ K :=
      Subgroup.eq_of_le_of_card_ge hVxP (by rw [hn, hVxcard]; norm_num)
    exact h1.trans h2.symm
  have hdvdK : 2 ^ n ∣ 360 := by
    rw [← hcard, ← hn]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hn3' : n = 3 := by
    by_contra hn4
    have : 4 ≤ n := by omega
    have h16 : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 this
    have := h16.trans hdvdK
    norm_num at this
  subst hn3'
  refine ⟨inf_le_right, hP2, ?_⟩
  have hcardP : Nat.card ↥((baum S ⊓ K).subgroupOf K) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hn]
    norm_num
  have hmul := Subgroup.card_mul_index ((baum S ⊓ K).subgroupOf K)
  rw [hcardP, hcard] at hmul
  intro h2
  obtain ⟨c, hc⟩ := h2
  omega

end U9Data

local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

theorem step9_facts
    {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {z u : G}
    {A V K : Subgroup G} (hP : Prop121Three) (cfg : A5Cfg G T M H S L)
    (D : U9Data T M H S L z u A V) (hK : IsComponentIn K (centralizerElem u))
    (hty : K9Type ↥K) (huzK : u * z ∈ K) :
    A ≤ K ∧ centralizerElem u ≤ Subgroup.normalizer (K : Set G) ∧
      IsSylowTwoOf (baum S ⊓ K) K ∧
      centralizerElem u ⊓ Subgroup.centralizer (K : Set G) =
        baum S ⊓ Subgroup.centralizer (K : Set G) ∧
      ∃ e : ↥K ≃* alternatingGroup (Fin 6), ∃ v : G,
        v ∈ blockU L ⊓ Subgroup.centralizer (A : Set G) ∧ v ≠ 1 ∧ v ≠ u ∧
          ∃ τ : Equiv.Perm (Fin 6), τ.IsSwap ∧ InducesPerm e v τ := by
  have hKq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hZK : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k = 1 := fun k hk hc =>
    congrArg Subtype.val (hty.center_trivial ⟨k, hk⟩ fun x' => Subtype.ext (hc x' x'.2))
  have hTu := D.Tu_le_normalizer hK huzK hZK
  have huG : u ∈ centralizerElem u := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hKnorm : centralizerElem u ≤ Subgroup.normalizer (K : Set G) := by
    have hs := cfg.cs.setting
    have hpc : pCoreOf 2 (centralizerElem u) ≠ ⊥ :=
      pCore_ne_bot_of_central huG D.u_ne_one D.u_sq' le_rfl
    rcases hP G hs.simple hs.nonabelian hs.qtke _ hpc K (mem_cComp_of_isComponentIn hK) with
      hn | ⟨hcard, -⟩
    · exact hn
    · exact (false_of_card_conj_eq_two D.s7.Tu_sylow hTu hcard).elim
  have hVK : V ≤ K := D.V_le_K hKnorm huzK
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := fun a ha => hKnorm (D.A_le_Hu ha).2
  obtain ⟨v, hvC, hv1, hvu⟩ := D.exists_v
  have hvU : v ∈ blockU L := hvC.1
  have hvA : ∀ a ∈ A, a * v = v * a := fun a ha => Subgroup.mem_centralizer_iff.mp hvC.2 a ha
  have hvGu : v ∈ centralizerElem u :=
    Subgroup.mem_centralizer_singleton_iff.mpr (D.U_comm v hvU u D.s7.u_U)
  have hvN : v ∈ Subgroup.normalizer (K : Set G) := hKnorm hvGu
  have hv2 : v * v = 1 := by rw [← pow_two]; exact D.U_sq v hvU
  let α : MulAut ↥K := conjSq hv2 hvN
  have hα2 : ∀ k, α (α k) = k := conjSq_sq hv2 hvN
  have hαne : ∃ k, α k ≠ k := by
    by_contra hfix
    push Not at hfix
    apply D.not_le_centralizer_v hKq hvC hv1 hvu
    intro k hk
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h1 : v⁻¹ * k * v = k := congrArg Subtype.val (hfix ⟨k, hk⟩)
    calc k * v = v * (v⁻¹ * k * v) := by group
      _ = v * k := by rw [h1]
  have hαV : ∀ (l : G) (hl : l ∈ V), α ⟨l, hVK hl⟩ = ⟨l, hVK hl⟩ := by
    intro l hl
    apply Subtype.ext
    show v⁻¹ * l * v = l
    calc v⁻¹ * l * v = v⁻¹ * (l * v) := by group
      _ = v⁻¹ * (v * l) := by rw [hvA l (D.V_le_A hl)]
      _ = l := by group
  have hαc : ∀ (c : G) (_ : c ∈ A) (hcN : c ∈ Subgroup.normalizer (K : Set G)) (k : ↥K),
      α (conjAutK c hcN k) = conjAutK c hcN (α k) := by
    intro c hc hcN k
    apply Subtype.ext
    show v⁻¹ * (c⁻¹ * (k : G) * c) * v = c⁻¹ * (v⁻¹ * (k : G) * v) * c
    have h : c * v = v * c := hvA c hc
    have hinv : v⁻¹ * c⁻¹ = c⁻¹ * v⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, h]
    calc v⁻¹ * (c⁻¹ * (k : G) * c) * v = (v⁻¹ * c⁻¹) * (k : G) * (c * v) := by group
      _ = (c⁻¹ * v⁻¹) * (k : G) * (v * c) := by rw [hinv, h]
      _ = c⁻¹ * (v⁻¹ * (k : G) * v) * c := by group
  rcases hty with ⟨⟨e₀⟩⟩ | ⟨⟨e₁⟩⟩ | h17
  · have hAK : A ≤ K :=
      D.A_le_K_of_A6 hKnorm hK.1 huzK hZK e₀ cfg.cs.setting.isPGroup
    have hcard : Nat.card ↥K = 360 := by
      rw [Nat.card_congr e₀.toEquiv]
      exact card_alt6'
    have hL12 : Nat.card ↥(A.subgroupOf K) = 12 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv]
      exact D.hA.card_L
    obtain ⟨e, he⟩ := exists_iso_swap e₀ α hα2 hαne (A.subgroupOf K) hL12 (fun l hl => by
      have hlA : (l : G) ∈ A := Subgroup.mem_subgroupOf.mp hl
      apply Subtype.ext
      show v⁻¹ * (l : G) * v = l
      calc v⁻¹ * (l : G) * v = v⁻¹ * ((l : G) * v) := by group
        _ = v⁻¹ * (v * (l : G)) := by rw [hvA l hlA]
        _ = l := by group)
    have hRC : baum S ≤ centralizerElem u := by
      rw [← D.s7.Su]
      exact inf_le_right
    refine ⟨hAK, hKnorm, D.RK_sylow hAK hTu cfg.cs.setting.isPGroup cfg.cs.le_T hcard, ?_, e, v,
      hvC, hv1, hvu, Equiv.swap 0 1, ⟨0, 1, by decide, rfl⟩, ?_⟩
    · apply le_antisymm
      · exact fun b hb => ⟨D.B_le_R huzK hVK hb, hb.2⟩
      · exact fun b hb => ⟨hRC hb.1, hb.2⟩
    · intro k k' hk
      have hk' : k' = α k := Subtype.ext hk
      rw [hk', he k, tau_eq_swap]
  · exfalso
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have hF : Nat.card (ZMod 7) = 7 := by simp
    obtain ⟨k, hk⟩ := hαne
    exact hk (psl2p_aut_eq_one (p := 7) (by norm_num) hF e₁ D.hA hVK hZK hAN α hαV hαc k)
  · exfalso
    obtain ⟨e₁⟩ := psl2_17_equiv h17
    have hF : Nat.card (GaloisField 17 1) = 17 := by
      have := GaloisField.card 17 1 (by norm_num)
      simpa using this
    obtain ⟨k, hk⟩ := hαne
    exact hk (psl2p_aut_eq_one (p := 17) (by norm_num) hF e₁ D.hA hVK hZK hAN α hαV hαc k)

end CFSG.QuasithinUnique.A5
