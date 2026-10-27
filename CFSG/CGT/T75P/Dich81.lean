module

public import CFSG.CGT.T75P.Type81
public import CFSG.CGT.T75P.AutNine
public import CFSG.CGT.T75Q.OrdersSL
public import CFSG.CGT.T75Q.ZCenter

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75Q CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem simple_card_dvd_factorial_index {K : Type*} [Group K] [Finite K] [IsSimpleGroup K]
    (M : Subgroup K) (hM : M ≠ ⊤) : Nat.card K ∣ M.index.factorial := by
  classical
  have hker : (MulAction.toPermHom K (K ⧸ M)).ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAction.toPermHom K (K ⧸ M)).ker with
      h | h
    · exact h
    · exfalso
      apply hM
      rw [eq_top_iff]
      intro k _
      have hk : k ∈ (MulAction.toPermHom K (K ⧸ M)).ker := by rw [h]; trivial
      have h1 := congrArg (fun f : Equiv.Perm (K ⧸ M) => f ((1 : K) : K ⧸ M))
        (MonoidHom.mem_ker.1 hk)
      have h2 : ((k : K) : K ⧸ M) = ((1 : K) : K ⧸ M) := by
        simpa [MulAction.toPermHom_apply] using h1
      have := QuotientGroup.eq.1 h2
      simpa using M.inv_mem this
  have hinj : Function.Injective (MulAction.toPermHom K (K ⧸ M)) :=
    (MonoidHom.ker_eq_bot_iff _).1 hker
  have := Subgroup.card_dvd_of_injective _ hinj
  rwa [Nat.card_perm, ← Subgroup.index_eq_card] at this

theorem Std81.eq_ugen_of_card (s : Std81 T T₁) {Y : Subgroup G} (hUY : ugen T ≤ Y)
    (hgen : Y ≤ Subgroup.closure (classD T ∩ (Y : Set G)))
    (hsimple : IsSimpleGroup (jQuot ↥Y)) (hcard : Nat.card (jQuot ↥Y) = 20160) :
    Y = ugen T := by
  classical
  have hfin : Finite G := s.finite
  have hWC := s.hc.hy.pair.wc
  obtain ⟨hTH, hHN, -⟩ := hSub_data T T₁
  have hHU : hSub T (normIn T₁ T) ≤ ugen T := hSub_le_ugen s.hc (by norm_num)
  have hker := s.ker_eq_center hUY hgen
  have hHcard := s.card_map_H hUY hgen
  have : Finite ↥Y := inferInstance
  set π := jMap ↥Y with hπ
  set Ĥ : Subgroup (jQuot ↥Y) := ((hSub T (normIn T₁ T)).subgroupOf Y).map π with hĤ
  set M : Subgroup (jQuot ↥Y) := ((ugen T).subgroupOf Y).map π with hM
  have hĤM : Ĥ ≤ M := Subgroup.map_mono (fun x hx => hHU hx)
  have hdvd1 : 1344 ∣ Nat.card M := hHcard ▸ Subgroup.card_dvd_of_le hĤM
  have hdvd2 : Nat.card M ∣ 20160 := hcard ▸ Subgroup.card_subgroup_dvd_card M
  have hMtop : M = ⊤ := by
    obtain ⟨k, hk⟩ := hdvd1
    have hk15 : k ∣ 15 := by
      have h' : 1344 * k ∣ 1344 * 15 := by rw [← hk]; exact hdvd2
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h'
    have hk' : k = 1 ∨ k = 3 ∨ k = 5 ∨ k = 15 := by
      have : k ≤ 15 := Nat.le_of_dvd (by norm_num) hk15
      interval_cases k <;> omega
    rcases hk' with rfl | rfl | rfl | rfl
    ·
      exfalso
      have hMĤ : Ĥ = M := Subgroup.eq_of_le_of_card_ge hĤM (by rw [hk, hHcard])
      obtain ⟨t₁, ht₁, ht₁N⟩ := s.exists_mem_T₁_not_normalizer
      apply ht₁N
      have ht₁Y : t₁ ∈ Y := hUY (s.T₁_le_ugen ht₁)
      have hmem : π ⟨t₁, ht₁Y⟩ ∈ M := ⟨⟨t₁, ht₁Y⟩, s.T₁_le_ugen ht₁, rfl⟩
      rw [← hMĤ] at hmem
      obtain ⟨h', hh', hh'π⟩ := Subgroup.mem_map.1 hmem
      have hz : h'⁻¹ * ⟨t₁, ht₁Y⟩ ∈ Subgroup.center ↥Y := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hh'π, inv_mul_cancel]
      have hzC : ((h'⁻¹ * ⟨t₁, ht₁Y⟩ : ↥Y) : G) ∈ Subgroup.centralizer (T : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have h1 := Subgroup.mem_center_iff.1 hz ⟨t, (T_le_ugen.trans hUY) ht⟩
        exact congrArg Subtype.val h1
      have heq : t₁ = (h' : G) * ((h'⁻¹ * ⟨t₁, ht₁Y⟩ : ↥Y) : G) := by
        have : (h' : ↥Y) * (h'⁻¹ * ⟨t₁, ht₁Y⟩) = ⟨t₁, ht₁Y⟩ := by group
        exact (congrArg Subtype.val this).symm
      rw [heq]
      exact (Subgroup.normalizer (T : Set G)).mul_mem (hHN (Subgroup.mem_subgroupOf.1 hh'))
        (Subgroup.centralizer_le_normalizer _ hzC)
    ·
      exfalso
      have hMne : M ≠ ⊤ := by
        intro h
        rw [h, Subgroup.card_top, hcard] at hk
        omega
      have hidx := Subgroup.card_mul_index M
      rw [hk, hcard] at hidx
      have h5 : M.index = 5 := by omega
      have := simple_card_dvd_factorial_index M hMne
      rw [hcard, h5] at this
      revert this
      decide
    ·
      exfalso
      have hMne : M ≠ ⊤ := by
        intro h
        rw [h, Subgroup.card_top, hcard] at hk
        omega
      have hidx := Subgroup.card_mul_index M
      rw [hk, hcard] at hidx
      have h3 : M.index = 3 := by omega
      have := simple_card_dvd_factorial_index M hMne
      rw [hcard, h3] at this
      revert this
      decide
    · exact Subgroup.eq_top_of_card_eq M (by rw [hk, hcard])
  have hTY : T ≤ Y := T_le_ugen.trans hUY
  refine le_antisymm ?_ hUY
  refine hgen.trans ((Subgroup.closure_le _).2 ?_)
  intro d hd
  obtain ⟨y, hy, t, ht, ht1, rfl⟩ := classD_inter_le_deltaOf hWC s.hN_gen s.h66' T_le_ugen
    s.exists_ne_one hUY hd.1 hd.2
  have hyM : π ⟨y, hy⟩ ∈ M := by rw [hMtop]; trivial
  obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.1 hyM
  have hz : u⁻¹ * ⟨y, hy⟩ ∈ Subgroup.center ↥Y := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, huy, inv_mul_cancel]
  have hzt := Subgroup.mem_center_iff.1 hz ⟨t, hTY ht⟩
  set z : G := ((u⁻¹ * ⟨y, hy⟩ : ↥Y) : G) with hzdef
  have h1 : t * z = z * t := congrArg Subtype.val hzt
  have hyu : (y : G) = (u : G) * z := by
    have : (u : ↥Y) * (u⁻¹ * ⟨y, hy⟩) = ⟨y, hy⟩ := by group
    exact (congrArg Subtype.val this).symm
  have hu' : (u : G) ∈ ugen T := Subgroup.mem_subgroupOf.1 hu
  have hconj : (y : G) * t * (y : G)⁻¹ = (u : G) * t * (u : G)⁻¹ := by
    rw [hyu]
    calc (u : G) * z * t * ((u : G) * z)⁻¹ = (u : G) * (z * t * z⁻¹) * (u : G)⁻¹ := by group
      _ = (u : G) * t * (u : G)⁻¹ := by rw [← h1]; group
  rw [hconj]
  exact (ugen T).mul_mem ((ugen T).mul_mem hu' (T_le_ugen ht)) ((ugen T).inv_mem hu')

theorem card_alt9 : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem card_alt8' : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem Std81.type_dich (s : Std81 T T₁) (hInd : SimpleCaseUpTo (Nat.card G))
    (h215 : Lemma215Stmt) (hL : ListWCIdentification) {Y : Subgroup G} (hY : GoodY T Y) :
    Y = ugen T ∨ Nonempty (jQuot ↥Y ≃* alternatingGroup (Fin 9)) := by
  have hUY : Uc T T₁ ≤ Y := s.Uc_le_ugen.trans hY.ugen_le
  have hcl := s.hcl_of_gen hY.ugen_le hY.gen
  obtain ⟨hsimple, -, -, -, -⟩ := ident81 s hInd h215 hL hUY hY.ne_top hcl
  rcases ident81_cases s hInd h215 hL hUY hY.ne_top hcl with h42 | h8 | h9
  · left
    obtain ⟨hadm, K', hF, hFin, hK', ⟨e⟩⟩ := h42
    have hK2 : Nat.card K' = 2 := by simpa using hK'
    refine s.eq_ugen_of_card hY.ugen_le hY.gen hsimple ?_
    rw [Nat.card_congr e.toEquiv, card_statedProj_of_card_two 4 hK2,
      CFSG.CGT.T75Q.card_SL_four_two hK2]
  · left
    obtain ⟨e⟩ := h8
    refine s.eq_ugen_of_card hY.ugen_le hY.gen hsimple ?_
    rw [Nat.card_congr e.toEquiv, card_alt8']
  · right
    exact h9

theorem Std81.eq_of_le_of_nine (s : Std81 T T₁) (hInd : SimpleCaseUpTo (Nat.card G))
    (h215 : Lemma215Stmt) (hL : ListWCIdentification) {Y₁ Y₂ : Subgroup G}
    (h₁ : GoodY T Y₁) (h₂ : GoodY T Y₂) (hle : Y₁ ≤ Y₂)
    (hnine : Nonempty (jQuot ↥Y₁ ≃* alternatingGroup (Fin 9))) : Y₁ = Y₂ := by
  classical
  have hfin : Finite G := s.finite
  have hWC := s.hc.hy.pair.wc
  rcases s.type_dich hInd h215 hL h₂ with h2U | h9
  · exact le_antisymm hle (h2U ▸ h₁.ugen_le)
  obtain ⟨e₁⟩ := hnine
  obtain ⟨e₂⟩ := h9
  have hk₁ := s.ker_eq_center h₁.ugen_le h₁.gen
  have hk₂ := s.ker_eq_center h₂.ugen_le h₂.gen
  have hc₁ : Nat.card (jQuot ↥Y₁) = 181440 := by rw [Nat.card_congr e₁.toEquiv, card_alt9]
  have hc₂ : Nat.card (jQuot ↥Y₂) = 181440 := by rw [Nat.card_congr e₂.toEquiv, card_alt9]
  let φ : ↥Y₁ →* jQuot ↥Y₂ := (jMap ↥Y₂).comp (Subgroup.inclusion hle)
  have hφker : φ.ker ≤ Subgroup.center ↥Y₁ := by
    intro y hy
    have hy' : Subgroup.inclusion hle y ∈ (jMap ↥Y₂).ker := hy
    rw [hk₂] at hy'
    rw [Subgroup.mem_center_iff]
    intro g
    have h3 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hy' (Subgroup.inclusion hle g))
    exact Subtype.ext h3
  have hidx₁ : (Subgroup.center ↥Y₁).index = 181440 := by
    rw [← hk₁, Subgroup.index_ker, MonoidHom.range_eq_top.2 jMap_surjective, Subgroup.card_top,
      hc₁]
  have hdvd : 181440 ∣ Nat.card φ.range := by
    have := Subgroup.index_dvd_of_le hφker
    rwa [hidx₁, Subgroup.index_ker] at this
  have hle2 : Nat.card φ.range ≤ 181440 := by
    have := Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card φ.range)
    omega
  have hrange : φ.range = ⊤ := by
    have h1 : Nat.card φ.range = 181440 := by
      obtain ⟨k, hk⟩ := hdvd
      have hpos : 0 < Nat.card φ.range := Nat.card_pos
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · omega
      · have : 181440 * 1 ≤ 181440 * k := Nat.mul_le_mul_left _ hk0
        omega
    exact Subgroup.eq_top_of_card_eq _ (by rw [h1, hc₂])
  have hTY₁ : T ≤ Y₁ := T_le_ugen.trans h₁.ugen_le
  refine le_antisymm hle ?_
  refine h₂.gen.trans ((Subgroup.closure_le _).2 ?_)
  intro d hd
  obtain ⟨y, hy, t, ht, ht1, rfl⟩ := classD_inter_le_deltaOf hWC s.hN_gen s.h66' T_le_ugen
    s.exists_ne_one h₂.ugen_le hd.1 hd.2
  have hmem : jMap ↥Y₂ ⟨y, hy⟩ ∈ φ.range := by rw [hrange]; trivial
  obtain ⟨y₁, hy₁⟩ := hmem
  have hz : (Subgroup.inclusion hle y₁)⁻¹ * ⟨y, hy⟩ ∈ Subgroup.center ↥Y₂ := by
    rw [← hk₂, MonoidHom.mem_ker, map_mul, map_inv]
    have : (jMap ↥Y₂) (Subgroup.inclusion hle y₁) = jMap ↥Y₂ ⟨y, hy⟩ := hy₁
    rw [this, inv_mul_cancel]
  set z : G := (((Subgroup.inclusion hle y₁)⁻¹ * ⟨y, hy⟩ : ↥Y₂) : G) with hzdef
  have hzt := Subgroup.mem_center_iff.1 hz ⟨t, h₂.ugen_le (T_le_ugen ht)⟩
  have h1 : t * z = z * t := congrArg Subtype.val hzt
  have hyu : y = (y₁ : G) * z := by
    have : (Subgroup.inclusion hle y₁) * ((Subgroup.inclusion hle y₁)⁻¹ * ⟨y, hy⟩) = ⟨y, hy⟩ := by
      group
    exact (congrArg Subtype.val this).symm
  have hconj : y * t * y⁻¹ = (y₁ : G) * t * (y₁ : G)⁻¹ := by
    rw [hyu]
    calc (y₁ : G) * z * t * ((y₁ : G) * z)⁻¹ = (y₁ : G) * (z * t * z⁻¹) * (y₁ : G)⁻¹ := by group
      _ = (y₁ : G) * t * (y₁ : G)⁻¹ := by rw [← h1]; group
  rw [hconj]
  exact Y₁.mul_mem (Y₁.mul_mem y₁.2 (hTY₁ ht)) (Y₁.inv_mem y₁.2)

theorem Std81.centralizes_of_normalizes (s : Std81 T T₁) {Y : Subgroup G} (hUY : ugen T ≤ Y)
    (hgen : Y ≤ Subgroup.closure (classD T ∩ (Y : Set G)))
    (e : jQuot ↥Y ≃* alternatingGroup (Fin 9)) {c : G}
    (hcC : c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G))
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) : ∀ y ∈ Y, c * y = y * c := by
  classical
  have hfin : Finite G := s.finite
  have hWC := s.hc.hy.pair.wc
  obtain ⟨hTH, hHN, -⟩ := hSub_data T T₁
  have hHY : hSub T (normIn T₁ T) ≤ Y := (hSub_le_ugen s.hc (by norm_num)).trans hUY
  have hTY : T ≤ Y := T_le_ugen.trans hUY
  have hcl := s.hcl_of_gen hUY hgen
  have htrans := natural_trans hHN s.hnat
  have hperf : commutator ↥Y = ⊤ :=
    commutator_eq_top_of_good hWC hTH hHY hHN s.hHC htrans s.not_isPGroup_H hcl
  have hker := s.ker_eq_center hUY hgen
  let θ : ↥Y ⧸ Subgroup.center ↥Y ≃* alternatingGroup (Fin 9) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective (jMap ↥Y) jMap_surjective).trans e)
  let α : MulAut ↥Y := Y.normalizerMonoidHom ⟨c, hcN⟩
  have hα : ∀ y : ↥Y, ((α y : ↥Y) : G) = c * y * c⁻¹ := fun y => by
    simp [α, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hα1 : α = 1 := by
    refine mulAut_eq_one_of_fixes_nine hperf θ α (T.subgroupOf Y)
      ((hSub T (normIn T₁ T)).subgroupOf Y) (fun x hx => hTH hx) ?_ ?_
      (s.T_inf_center hHY) ?_ ?_
    · rw [← s.card_T]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv
    · intro a ha b hb
      exact Subtype.ext (elemAbelian_mul_comm hWC.1 ha hb)
    · intro a ha ha1 b hb hb1
      have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
      have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
      obtain ⟨h, hh, hhab⟩ := htrans (a : G) ha ha1' (b : G) hb hb1'
      exact ⟨⟨h, hHY hh⟩, hh, Subtype.ext hhab⟩
    · intro h hh
      apply Subtype.ext
      rw [hα]
      have := Subgroup.mem_centralizer_iff.1 hcC (h : G) hh
      calc c * (h : G) * c⁻¹ = (h : G) * c * c⁻¹ := by rw [this]
        _ = h := by group
  intro y hy
  have h1 := congrArg (fun a : MulAut ↥Y => ((a ⟨y, hy⟩ : ↥Y) : G)) hα1
  simp only [hα, MulAut.one_apply] at h1
  calc c * y = c * y * c⁻¹ * c := by group
    _ = y * c := by rw [h1]

theorem Std81.Z_odd (s : Std81 T T₁) {Y : Subgroup G} (hUY : ugen T ≤ Y)
    (hgen : Y ≤ Subgroup.closure (classD T ∩ (Y : Set G)))
    (hCY : ∀ c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G), c ∈ Y →
      ∀ u ∈ Y, c * u = u * c) : Odd (Nat.card (Subgroup.center ↥Y)) := by
  have hfin : Finite G := s.finite
  obtain ⟨hTH, hHN, -⟩ := hSub_data T T₁
  have hHY : hSub T (normIn T₁ T) ≤ Y := (hSub_le_ugen s.hc (by norm_num)).trans hUY
  exact odd_card_center_of_good s.hc.hy.pair.wc hTH hHY hHN s.hHC (natural_trans hHN s.hnat)
    s.not_isPGroup_H (fun g hg => normalizer_eq_mul s.h62 s.h63 s.hc s.hnat chain3 hg)
    (inf_hSub_centralizer_eq_bot s.hc s.hnat) hCY (s.hcl_of_gen hUY hgen)

theorem no_involution_of_odd_center {Y : Subgroup G} (hodd : Odd (Nat.card (Subgroup.center ↥Y))) :
    ∀ c ∈ Y ⊓ Subgroup.centralizer (Y : Set G), c * c = 1 → c = 1 := by
  intro c hc hcc
  by_contra hc1
  have hz : (⟨c, hc.1⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hc.2 (g : G) g.2)
  let z : ↥(Subgroup.center ↥Y) := ⟨⟨c, hc.1⟩, hz⟩
  have hz2 : z ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [pow_two] using hcc
  have hz1 : z ≠ 1 := fun h => hc1 (congrArg (fun w : ↥(Subgroup.center ↥Y) => ((w : ↥Y) : G)) h)
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hdvd : orderOf z ∣ Nat.card (Subgroup.center ↥Y) := orderOf_dvd_natCard z
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

end CFSG.CGT.T75P
