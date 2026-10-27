module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Remark31Fstar
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S7A
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

section Generic

variable {G : Type} [Group G]

theorem zpowers_isElemAbelian {u : G} (hu2 : u * u = 1) :
    IsElemAbelian 2 (Subgroup.zpowers u) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨i, hi⟩ := x.2
    obtain ⟨j, hj⟩ := y.2
    apply Subtype.ext
    show (x : G) * y = y * x
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self u i j).eq
  · rcases (mem_zpowers_two hu2 x).mp hx with h | h
    · rw [h]
      simp
    · rw [h, pow_two, hu2]

theorem isElemAbelian_sup_of_commute {A B : Subgroup G} (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian 2 (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hAB

variable [Finite G]

theorem exists_E32 {L₁ U₁ L₂ U₂ : Subgroup G} (h₁ : IsA4Block L₁ U₁) (h₂ : IsA4Block L₂ U₂)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) {u : G} (hu1 : u ≠ 1) (hu2 : u * u = 1)
    (huL₁ : ∀ a ∈ L₁, a * u = u * a) (huL₂ : ∀ b ∈ L₂, b * u = u * b) :
    ∃ E : Subgroup G, E ≤ Subgroup.zpowers u ⊔ (U₁ ⊔ U₂) ∧ IsElemAbelian 2 E ∧
      Nat.card E = 32 := by
  have hU₁₂ : ∀ a ∈ U₁, ∀ b ∈ U₂, a * b = b * a := fun a ha b hb =>
    hcomm a (h₁.le ha) b (h₂.le hb)
  have hU₁N : U₁ ≤ Subgroup.normalizer (U₂ : Set G) := C5.le_normalizer_of_commute hU₁₂
  obtain ⟨c₁, hc₁L, -, -, hc₁fp, -⟩ := h₁.exists_c
  obtain ⟨c₂, hc₂L, -, -, hc₂fp, -⟩ := h₂.exists_c
  have hbot : U₁ ⊓ U₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx₁, hx₂⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    apply hc₁fp x hx₁ hx1
    have := hcomm c₁ hc₁L x (h₂.le hx₂)
    calc c₁ * x * c₁⁻¹ = x * c₁ * c₁⁻¹ := by rw [this]
      _ = x := by group
  have hW : Nat.card ↥(U₁ ⊔ U₂) = 16 := by
    have := C5.card_sup_mul_card_inf_of_le_normalizer hU₁N
    rw [hbot, Subgroup.card_bot, h₁.card_U, h₂.card_U] at this
    omega
  have hWc : U₁ ⊔ U₂ ≤ Subgroup.centralizer ({u} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact (huL₁ a (h₁.le ha)).symm
    · refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact (huL₂ b (h₂.le hb)).symm
  have hzN : Subgroup.zpowers u ≤ Subgroup.normalizer ((U₁ ⊔ U₂ : Subgroup G) : Set G) := by
    refine C5.le_normalizer_of_commute fun y hy w hw => ?_
    have hy' : y ∈ Subgroup.zpowers u := hy
    rcases (mem_zpowers_two hu2 y).mp hy' with h | h
    · rw [h]
      simp
    · rw [h]
      exact (Subgroup.mem_centralizer_iff.mp (hWc hw) u rfl)
  have hyw : ∀ y ∈ Subgroup.zpowers u, ∀ w ∈ U₁ ⊔ U₂, y * w = w * y := by
    intro y hy w hw
    rcases (mem_zpowers_two hu2 y).mp hy with h | h
    · rw [h]
      simp
    · rw [h]
      exact (Subgroup.mem_centralizer_iff.mp (hWc hw) u rfl)
  have hzW : Subgroup.zpowers u ⊓ (U₁ ⊔ U₂) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hxW⟩
    rw [Subgroup.mem_bot]
    rcases (mem_zpowers_two hu2 x).mp hx with h | h
    · exact h
    · exfalso
      have hxW' : x ∈ ((U₁ ⊔ U₂ : Subgroup G) : Set G) := hxW
      rw [Subgroup.coe_mul_of_left_le_normalizer_right U₁ U₂ hU₁N] at hxW'
      obtain ⟨a, ha, b, hb, hab⟩ := hxW'
      have hab' : a * b = u := hab.trans h
      have hc₁b : c₁ * b = b * c₁ := hcomm c₁ hc₁L b (h₂.le hb)
      have hc₂a : c₂ * a = a * c₂ := (hcomm a (h₁.le ha) c₂ hc₂L).symm
      have hc₁u : c₁ * u = u * c₁ := huL₁ c₁ hc₁L
      have hc₂u : c₂ * u = u * c₂ := huL₂ c₂ hc₂L
      have hb' : c₁ * b * c₁⁻¹ = b := by
        calc c₁ * b * c₁⁻¹ = b * c₁ * c₁⁻¹ := by rw [hc₁b]
          _ = b := by group
      have hu' : c₁ * u * c₁⁻¹ = u := by
        calc c₁ * u * c₁⁻¹ = u * c₁ * c₁⁻¹ := by rw [hc₁u]
          _ = u := by group
      have ha' : c₂ * a * c₂⁻¹ = a := by
        calc c₂ * a * c₂⁻¹ = a * c₂ * c₂⁻¹ := by rw [hc₂a]
          _ = a := by group
      have hu'' : c₂ * u * c₂⁻¹ = u := by
        calc c₂ * u * c₂⁻¹ = u * c₂ * c₂⁻¹ := by rw [hc₂u]
          _ = u := by group
      have key1 : (c₁ * a * c₁⁻¹) * b = a * b := by
        calc (c₁ * a * c₁⁻¹) * b = (c₁ * a * c₁⁻¹) * (c₁ * b * c₁⁻¹) := by rw [hb']
          _ = c₁ * (a * b) * c₁⁻¹ := by group
          _ = c₁ * u * c₁⁻¹ := by rw [hab']
          _ = u := hu'
          _ = a * b := hab'.symm
      have key2 : a * (c₂ * b * c₂⁻¹) = a * b := by
        calc a * (c₂ * b * c₂⁻¹) = (c₂ * a * c₂⁻¹) * (c₂ * b * c₂⁻¹) := by rw [ha']
          _ = c₂ * (a * b) * c₂⁻¹ := by group
          _ = c₂ * u * c₂⁻¹ := by rw [hab']
          _ = u := hu''
          _ = a * b := hab'.symm
      have ha1 : a = 1 := by
        by_contra ha1
        exact hc₁fp a ha ha1 (mul_right_cancel key1)
      have hb1 : b = 1 := by
        by_contra hb1
        exact hc₂fp b hb hb1 (mul_left_cancel key2)
      apply hu1
      rw [← hab', ha1, hb1, one_mul]
  refine ⟨Subgroup.zpowers u ⊔ (U₁ ⊔ U₂), le_rfl,
    isElemAbelian_sup_of_commute (zpowers_isElemAbelian hu2)
      (isElemAbelian_sup_of_commute h₁.isElemAbelian_U h₂.isElemAbelian_U hU₁₂) hyw, ?_⟩
  have hcard := C5.card_sup_mul_card_inf_of_le_normalizer hzN
  rw [hzW, Subgroup.card_bot, Nat.card_zpowers, orderOf_eq_prime ((pow_two u).trans hu2) hu1,
    hW] at hcard
  omega

end Generic

section A5

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem rank_le_sixteen (h247 : Lemma2_4_27) (cfg : A5Cfg G T M H S L)
    {r : G} (hrS : r ∈ S) (hrR : r ∉ baum S) {E : Subgroup G} (hET : E ≤ T)
    (hE : IsElemAbelian 2 E) : Nat.card E ≤ 16 := by
  obtain ⟨x, hxT, hxS⟩ := C.exists_mem_T_sdiff
  obtain ⟨-, h2, -⟩ := h247 G T M H S L cfg.cs (Or.inl ⟨cfg.alt5, cfg.single⟩)
  obtain ⟨A₁, -, hA⟩ := h2 x hxT hxS r hrS hrR
  have hmax : IsMaxElemAbelian T (pCoreOf 2 H) := (hA _).mpr (Or.inl rfl)
  have h1 := hmax.2.2 E hET hE
  rw [C.Q_eq_U X.hTC, C.card_U] at h1
  exact h1

end A5

section Excl

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_map_equiv {E : Subgroup G} (f : G ≃* G) (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E.map f.toMonoidHom) := CFSG.Open.IsElemAbelian.map hE _

theorem false_of_A5_two_group
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h2425 : Lemma2_4_25) {T M P S' L' : Subgroup G}
    (hcs : ConstrainedSetting G T M P S' L') (h5 : IsAltType L' 5)
    (h2 : ∀ g ∈ P ⊓ M, ∃ k : ℕ, g ^ 2 ^ k = 1) : False := by
  have hj := h2425 G T M P S' L' hcs h5
  have F := h247_facts h247 hcs h5 hj
  have hQ := blockQ_eq_blockU h245_4 hcs hj
  obtain ⟨D, hsurj, hker, hRE, hRE', hHeq⟩ := exists_stdData hcs hj h5 F hQ hC54
  let C : StdCfg T M P S' L' := ⟨hcs, hj, F, D, hsurj, hker, hRE, hRE', hHeq⟩
  obtain ⟨h, hh⟩ := hsurj c3
  have hM : (h : G) ∈ M := C.mem_M_of_pi_mem h (by
    show D.π h ∈ S4std
    rw [hh]
    exact (mem_S4std c3).mpr c3_four)
  obtain ⟨k, hk⟩ := h2 h ⟨h.2, hM⟩
  have h1 : h ^ 2 ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hk)
  have h2' : c3 ^ 2 ^ k = 1 := by rw [← hh, ← map_pow, h1, map_one]
  have hdvd : orderOf c3 ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2'
  have hord : orderOf c3 = 3 := orderOf_eq_prime c3_cube c3_ne
  rw [hord] at hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

end Excl

theorem lemma2_4_29_8
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) (h2425 : Lemma2_4_25) (hSA : ConstrainedSetupAt)
    (hlin : Lin2BlockExcluded) (ha3 : SingleA3Excluded) : Lemma2_4_29_8 := by
  intro G _ _ T M H S L cfg z u s hct
  obtain ⟨C, ⟨X⟩⟩ := a5_exists_sec h247 h245_4 hC54 h314 cfg
  have hcs := cfg.cs
  have hTu2 : IsPGroup 2 ↥(T ⊓ centralizerElem u) := hcs.setting.isPGroup.to_le inf_le_left
  have hGM : centralizerElem u ⊓ M = T ⊓ centralizerElem u := by
    rw [inf_comm, ← s.Tu_eq]
  have hsyl : IsSylowTwoOf (T ⊓ centralizerElem u) (centralizerElem u ⊓ M) := by
    rw [hGM]
    exact ⟨le_rfl, hTu2, by rw [Subgroup.subgroupOf_self, Subgroup.index_top]; norm_num⟩
  obtain ⟨P, L', hPG, hcs'⟩ := hSA G T M (centralizerElem u) (T ⊓ centralizerElem u)
    hcs.setting hcs.notBender hcs.notSmall (Or.inr s.Gu_gamma2) hct hsyl inf_le_left
  rcases hcs'.block.2 with ⟨n, hn, hlin2⟩ | h3 | h5
  · exact hlin G T M P _ L' hcs' n hn hlin2
  · by_cases hj : conjJoin (T ⊓ centralizerElem u) L' = L'
    · exact ha3 G T M P _ L' hcs' h3 hj
    · obtain ⟨s', hcfg'⟩ := exists_A3A3 hcs' h3 hj
      have h₁ : IsA4Block L' (blockU L') := IsA4Block.of_alt3 (C56.isShort hcs') hcfg'.a3
      have h₂ := h₁.conj s'
      have hLP : L' ≤ P := C56.le_H hcs'
      have hL₂P : conjR L' s' ≤ P := by
        have : conjJoin (T ⊓ centralizerElem u) L' ≤ P := by
          rw [hcs'.eq_join]
          exact le_sup_left
        rw [hcfg'.join] at this
        exact le_sup_right.trans this
      have hcomm : ∀ a ∈ L', ∀ b ∈ conjR L' s', a * b = b * a := by
        have h0 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcfg'.comm
        intro a ha b hb
        exact (Subgroup.mem_centralizer_iff.mp (h0 ha) b hb).symm
      have huC : ∀ g ∈ P, g * u = u * g := by
        intro g hg
        exact Subgroup.mem_centralizer_singleton_iff.mp (hPG hg)
      have hu1 : u ≠ 1 := fun h1 => s.u_not (h1 ▸ one_mem _)
      have hu2 : u * u = 1 := by
        have := hcs.block.1.1.2.2.1.2 u s.u_U
        rwa [pow_two] at this
      have huL₁ : ∀ a ∈ L', a * u = u * a := fun a ha => huC a (hLP ha)
      have huL₂ : ∀ b ∈ conjR L' s', b * u = u * b := fun b hb => huC b (hL₂P hb)
      obtain ⟨E, hEle, hEab, hE32⟩ := exists_E32 h₁ h₂ hcomm hu1 hu2 huL₁ huL₂
      have huCu : u ∈ centralizerElem u := Subgroup.mem_centralizer_iff.2 fun g hg => by
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
      have hEC : E ≤ centralizerElem u := by
        refine hEle.trans (sup_le (Subgroup.zpowers_le.mpr huCu) (sup_le ?_ ?_))
        · exact fun a ha => hPG (hLP (h₁.le ha))
        · exact fun b hb => hPG (hL₂P (h₂.le hb))
      have hE2 : IsPGroup 2 ↥E := IsPGroup.of_card (n := 5) (by rw [hE32]; norm_num)
      obtain ⟨P', hEP', hP'⟩ := exists_isSylowTwoOf_of_le hEC hE2
      obtain ⟨h, -, hP'eq⟩ := s.Tu_sylow.exists_conj hP'
      have hE'T : E.map (MulAut.conj h⁻¹).toMonoidHom ≤ T := by
        rintro _ ⟨e, he, rfl⟩
        have he' : e ∈ P' := hEP' he
        rw [hP'eq] at he'
        obtain ⟨t, ht, hte⟩ := he'
        have hte' : h * t * h⁻¹ = e := hte
        show h⁻¹ * e * h⁻¹⁻¹ ∈ T
        rw [inv_inv, ← hte']
        have : h⁻¹ * (h * t * h⁻¹) * h = t := by group
        rw [this]
        exact ht.1
      have hE'ab := isElemAbelian_map_equiv (MulAut.conj h⁻¹) hEab
      have hcard : Nat.card (E.map (MulAut.conj h⁻¹).toMonoidHom) = 32 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective, hE32]
      obtain ⟨r, hrS, hrR, -⟩ := s.s_exists
      have := rank_le_sixteen X h247 cfg hrS hrR hE'T hE'ab
      omega
  · refine false_of_A5_two_group h247 h245_4 hC54 h2425 hcs' h5 (fun g hg => ?_)
    have hgC : g ∈ centralizerElem u := hPG hg.1
    have hgT : g ∈ T ⊓ centralizerElem u := by
      rw [← hGM]
      exact ⟨hgC, hg.2⟩
    obtain ⟨k, hk⟩ := hcs.setting.isPGroup ⟨g, hgT.1⟩
    exact ⟨k, congrArg Subtype.val hk⟩

end CFSG.QuasithinUnique.A5
