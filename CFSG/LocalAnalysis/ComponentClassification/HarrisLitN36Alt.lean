module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Normal
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36AltPerm
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36AltCover
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinAlt

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup Equiv Equiv.Perm GrSLit.L34Facts GSThmB.Catalog82A10
open CFSG.ComponentClassification.HarrisLit.Hin

theorem false_of_dvd_360 {N q c : ℕ} (hc : c ∣ 360) (hc' : c ≠ 360) (hN : N ∣ c) (hq7 : 7 ≤ q)
    (h : N * 2 = q * (q ^ 2 - 1)) : False := by
  have hc0 : 0 < c := Nat.pos_of_dvd_of_pos hc (by norm_num)
  have hc180 : c ≤ 180 := by
    obtain ⟨k, hk⟩ := hc
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with hk' | hk'
      · interval_cases k <;> omega
      · exact hk'
    nlinarith
  have hNc : N ≤ c := Nat.le_of_dvd hc0 hN
  have hq : q = 7 := by
    by_contra hne
    have h8 : 8 ≤ q := by omega
    have : 8 * (8 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul h8 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h8 2) 1)
    omega
  subst hq
  obtain ⟨k, hk⟩ := hN
  obtain ⟨j, hj⟩ := hc
  have hN168 : N = 168 := by norm_num at h; omega
  subst hN168
  have hk1 : k = 1 := by omega
  subst hk1
  rw [hk] at hj
  omega

theorem eq_bot_of_normal_of_sq_eq_one {H : Type*} [Group H] [Finite H]
    [IsSimpleGroup (H ⧸ pPrimeCore 2 H)] (hna : ∃ a b : H ⧸ pPrimeCore 2 H, a * b ≠ b * a)
    (M : Subgroup H) [hM : M.Normal] (hc : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (h2 : ∀ x ∈ M, x * x = 1) : M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMn : (M.map (QuotientGroup.mk' (pPrimeCore 2 H))).Normal :=
    hM.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (pPrimeCore 2 H))) with
    hb | ht
  · rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    have hxO : x ∈ pPrimeCore 2 H := by
      have h1 : QuotientGroup.mk' (pPrimeCore 2 H) x ∈
          M.map (QuotientGroup.mk' (pPrimeCore 2 H)) := ⟨x, hx, rfl⟩
      rw [hb, mem_bot] at h1
      exact (QuotientGroup.eq_one_iff x).mp h1
    have hodd : Nat.Coprime 2 (orderOf x) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hxO) pPrimeCore_coprime_card
    have hx2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2 x hx)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hodd.symm hx2)
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    obtain ⟨a', ha', rfl⟩ : a ∈ M.map (QuotientGroup.mk' (pPrimeCore 2 H)) := ht ▸ mem_top a
    obtain ⟨b', hb', rfl⟩ : b ∈ M.map (QuotientGroup.mk' (pPrimeCore 2 H)) := ht ▸ mem_top b
    exact hab (by rw [← map_mul, ← map_mul, hc a' ha' b' hb'])

namespace Config

variable {G : Type} [Group G] [Finite G] {p m : ℕ} {τ : MulAut G} {K : Subgroup G}

theorem card_quot_bar (h : Config G p m τ K) :
    Nat.card (↥(K.map (QuotientGroup.mk' (center G))) ⧸
      pPrimeCore 2 ↥(K.map (QuotientGroup.mk' (center G)))) * 2 =
      p ^ m * ((p ^ m) ^ 2 - 1) := by
  obtain ⟨hpP, hm1, -, F', _, _, hF', ⟨eL⟩⟩ := exists_psl2_of_lieModel h.lieModel_bar
  have hodd := AutL2Facts.isOddPrimePower_of hpP h.ne_two hm1 hF'
  rw [Nat.card_congr eL.toEquiv, GorensteinWalter.psl2_card_formula F' hodd, hF']
  have hev : 2 ∣ p ^ m * ((p ^ m) ^ 2 - 1) := by
    have h2 : 2 ∣ (p ^ m) ^ 2 - 1 := by
      have : 16 ∣ (p ^ m) ^ 2 - 1 := by have := h.sixteen_dvd; rwa [← pow_mul, mul_comm]
      exact (by norm_num : 2 ∣ 16).trans this
    exact h2.mul_left _
  exact Nat.div_mul_cancel hev

end Config

theorem rowFor_alt : RowFor IsAlt := by
  intro G _ _ p m τ K h ⟨n, hn5, ⟨e⟩⟩
  exfalso
  classical
  have := h.simple_bar
  have := h.perfect
  set σ := quotAut τ with hσdef
  set Kb := K.map (QuotientGroup.mk' (center G)) with hKbdef
  set C := fixedPoints σ with hCdef
  have hKC : Kb ≤ C := h.isTwoComponentIn_bar.1
  have h168 : 168 ≤ Nat.card (↥Kb ⧸ pPrimeCore 2 ↥Kb) :=
    le_card_of_lieModel_psl2_sixteen h.ne_two h.sixteen_dvd h.lieModel_bar
  have hKq : Nat.card (↥Kb ⧸ pPrimeCore 2 ↥Kb) ∣ Nat.card ↥Kb :=
    ⟨_, Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩
  have hσ1 : σ ≠ 1 := by
    intro h1
    have h2 := h.orderOf_bar
    rw [← hσdef, h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hnt : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcardY : Nat.card (G ⧸ center G) = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  by_cases hn6 : n ≤ 6
  ·
    have hCdvd : Nat.card ↥C ∣ n.factorial / 2 := hcardY ▸ Subgroup.card_subgroup_dvd_card C
    have hCne : Nat.card ↥C ≠ n.factorial / 2 := by
      intro hc
      apply hσ1
      have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C (hc.trans hcardY.symm)
      ext y
      have hy : y ∈ C := htop ▸ mem_top y
      exact hy
    have hN : Nat.card (↥Kb ⧸ pPrimeCore 2 ↥Kb) ∣ Nat.card ↥C :=
      hKq.trans (Subgroup.card_dvd_of_le hKC)
    have hNq := h.card_quot_bar
    interval_cases n
    · rw [show Nat.factorial 5 / 2 = 60 by decide] at hCdvd
      have h60 := Nat.le_of_dvd (by norm_num) hCdvd
      have := Nat.le_of_dvd Nat.card_pos hN
      omega
    · rw [show Nat.factorial 6 / 2 = 360 by decide] at hCdvd hCne
      exact false_of_dvd_360 hCdvd hCne hN h.seven_le hNq
  push Not at hn6
  have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 (by omega)
  set κ : Perm (Fin n) →* MulAut (alternatingGroup (Fin n)) := MulAut.conjNormal with hκ
  obtain ⟨π, hπ⟩ := hbij.2 (MulAut.congr e σ)
  have hππ : π * π = 1 := by
    apply hbij.1
    rw [map_mul, hπ, map_one, ← map_mul]
    have hsq : σ * σ = 1 := by
      have := pow_orderOf_eq_one σ
      rw [h.orderOf_bar, pow_two] at this
      exact this
    rw [hsq, map_one]
  have hmemC : ∀ y : G ⧸ center G, y ∈ C ↔
      (e y : Perm (Fin n)) * π = π * (e y : Perm (Fin n)) := by
    intro y
    have h1 : e (σ y) = κ π (e y) := by
      rw [hπ]
      change e (σ y) = e (σ (e.symm (e y)))
      rw [MulEquiv.symm_apply_apply]
    have h2 : ((κ π (e y) : alternatingGroup (Fin n)) : Perm (Fin n)) =
        π * (e y : Perm (Fin n)) * π⁻¹ := MulAut.conjNormal_apply π (e y)
    change σ y = y ↔ _
    constructor
    · intro hy
      have h3 : π * (e y : Perm (Fin n)) * π⁻¹ = (e y : Perm (Fin n)) := by
        rw [← h2, ← h1, hy]
      calc (e y : Perm (Fin n)) * π = π * (e y : Perm (Fin n)) * π⁻¹ * π := by rw [h3]
        _ = π * (e y : Perm (Fin n)) := by group
    · intro hy
      apply e.injective
      apply Subtype.ext
      rw [h1, h2, ← hy, mul_inv_cancel_right]
  set LP : Subgroup (Perm (Fin n)) :=
    (Kb.map e.toMonoidHom).map (alternatingGroup (Fin n)).subtype with hLPdef
  let eLP : ↥Kb ≃* ↥LP := (Kb.equivMapOfInjective _ e.injective).trans
    ((Kb.map e.toMonoidHom).equivMapOfInjective _ (alternatingGroup (Fin n)).subtype_injective)
  have hKbperf : ⁅Kb, Kb⁆ = Kb := by
    have hp : Group.IsPerfect ↥Kb := h.isTwoComponentIn_bar.2.2.1
    have hc := congrArg (Subgroup.map Kb.subtype) hp.commutator_eq_top
    rwa [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hc
  have hLPperf : ⁅LP, LP⁆ = LP := by
    rw [hLPdef, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hKbperf]
  have hLPC : ∀ g ∈ LP, g * π = π * g := by
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact (hmemC l).mp (hKC hl)
  have hLPn : ∀ x ∈ alternatingGroup (Fin n), x * π = π * x → ∀ g ∈ LP, x * g * x⁻¹ ∈ LP := by
    rintro x hxA hxπ _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    set y := e.symm ⟨x, hxA⟩ with hydef
    have hey : (e y : Perm (Fin n)) = x := by rw [hydef, MulEquiv.apply_symm_apply]
    have hyC : y ∈ C := by
      rw [hmemC, hey]
      exact hxπ
    have hconj : y * l * y⁻¹ ∈ Kb := by
      have h1 := h.bar_normal.conj_mem ⟨l, hKC hl⟩ (by rw [mem_subgroupOf]; exact hl) ⟨y, hyC⟩
      rw [mem_subgroupOf] at h1
      exact h1
    refine ⟨e (y * l * y⁻¹), ⟨y * l * y⁻¹, hconj, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, Subgroup.coe_subtype, hey]
  have hs := isSimpleGroup_of_lieModel_psl2 h.lieModel_bar
  have hna := nonabelian_of_lieModel_psl2 h.lieModel_bar
  let ι : ↥Kb →* Perm (Fin n) := LP.subtype.comp eLP.toMonoidHom
  have hι : Function.Injective ι := LP.subtype_injective.comp eLP.injective
  have hιLP : ∀ k, ι k ∈ LP := fun k => (eLP k).2
  have hLPB : ∀ g ∈ LP, g ∈ pairSub hππ → g = 1 := by
    set M : Subgroup ↥Kb := (pairSub hππ).comap ι with hMdef
    have hMn : M.Normal := ⟨fun a ha b => by
      rw [hMdef, mem_comap] at ha ⊢
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_pairSub hππ (hLPC _ (hιLP b)) ha⟩
    have hMc : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := fun a ha b hb =>
      hι (by rw [map_mul, map_mul]; exact pairSub_comm hππ ha hb)
    have hM2 : ∀ a ∈ M, a * a = 1 := fun a ha =>
      hι (by rw [map_mul, map_one]; exact pairSub_sq hππ ha)
    have hMbot := eq_bot_of_normal_of_sq_eq_one hna M hMc hM2
    intro g hg hgB
    obtain ⟨k, hk⟩ := eLP.surjective ⟨g, hg⟩
    have hkM : k ∈ M := by
      rw [hMdef, mem_comap]
      show ((eLP k : ↥LP) : Perm (Fin n)) ∈ pairSub hππ
      rw [hk]
      exact hgB
    rw [hMbot, mem_bot] at hkM
    rw [hkM, map_one] at hk
    exact (congrArg Subtype.val hk).symm
  have hLPalt : LP ≤ altOn π.supportᶜ := le_altOn_of_inf_eq_bot hππ hLPperf hLPC
    (fun x hx hxA => hLPn x hxA (mem_centralizer_singleton_iff.mp
      (pairSub_le_centralizer hππ hx))) hLPB
  set T := π.supportᶜ with hTdef
  have hLP168 : 168 ≤ Nat.card ↥LP := by
    rw [← Nat.card_congr eLP.toEquiv]
    exact h168.trans (Nat.le_of_dvd Nat.card_pos hKq)
  have hT6 : 6 ≤ T.card := by
    by_contra hlt
    push Not at hlt
    have h60 := card_altOn_le_sixty (T := T) (by omega)
    have hle := Subgroup.card_le_of_le hLPalt
    omega
  have hTs : IsSimpleGroup ↥(altOn T) := isSimpleGroup_altOn T (by omega)
  have hLPnT : (LP.subgroupOf (altOn T)).Normal := ⟨fun a ha b => by
    rw [mem_subgroupOf] at ha ⊢
    have hb := mem_altOn.mp b.2
    have h1 := hLPn b hb.1 (commute_of_support_subset_compl hb.2) a ha
    simpa using h1⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (LP.subgroupOf (altOn T)) with hb | ht
  · have hLPbot : LP = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have h1 : (⟨g, hLPalt hg⟩ : ↥(altOn T)) ∈ LP.subgroupOf (altOn T) := hg
      rw [hb, mem_bot] at h1
      exact (mem_bot).mpr (congrArg Subtype.val h1)
    rw [hLPbot, card_bot] at hLP168
    omega
  have hAltLP : altOn T ≤ LP := fun x hx => by
    have h1 : (⟨x, hx⟩ : ↥(altOn T)) ∈ LP.subgroupOf (altOn T) := ht ▸ mem_top _
    exact h1
  obtain ⟨t4, ht4T, ht4c⟩ := Finset.exists_subset_card_eq (show 4 ≤ T.card by omega)
  let f : Fin 4 → Fin n := fun i => t4.orderEmbOfFin ht4c i
  have hf : Function.Injective f := (t4.orderEmbOfFin ht4c).injective
  have hfT : ∀ i, f i ∈ T := fun i => ht4T (t4.orderEmbOfFin_mem ht4c i)
  have hne : ∀ i j : Fin 4, i ≠ j → f i ≠ f j := fun i j hij => hf.ne hij
  have hδA : swap (f 0) (f 1) * swap (f 2) (f 3) ∈ altOn T := by
    rw [mem_altOn]
    refine ⟨?_, ?_⟩
    · rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (hne 0 1 (by decide)),
        Perm.sign_swap (hne 2 3 (by decide))]
      decide
    · intro x hx
      have hx' := Perm.support_mul_le (swap (f 0) (f 1)) (swap (f 2) (f 3)) hx
      rw [Finset.sup_eq_union, Finset.mem_union, support_swap (hne 0 1 (by decide)),
        support_swap (hne 2 3 (by decide))] at hx'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with (rfl | rfl) | (rfl | rfl) <;> exact hfT _
  obtain ⟨_, ⟨kb, hkb, rfl⟩, hkbδ⟩ := hAltLP hδA
  obtain ⟨k, hk, rfl⟩ := hkb
  let η : G →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center G := by
    ext g
    simp [η]
  have hηk : ((η k : alternatingGroup (Fin n)) : Perm (Fin n)) =
      swap (f 0) (f 1) * swap (f 2) (f 3) := hkbδ
  have hk2 : k ^ 2 = 1 := by
    have h1 : k ^ 2 ∈ center G := by
      rw [← hker, MonoidHom.mem_ker, map_pow]
      apply Subtype.ext
      rw [Subgroup.coe_pow, hηk, OneMemClass.coe_one]
      exact LocalAnalysis.ComponentInitial.swap_mul_swap_sq_of_ne (hne 0 2 (by decide))
        (hne 0 3 (by decide)) (hne 2 1 (by decide)) (hne 1 3 (by decide))
    have h2 : k ^ 2 ∈ K ⊓ center G := ⟨K.pow_mem hk 2, h1⟩
    rw [h.inf_center, mem_bot] at h2
    exact h2
  exact sq_ne_one_of_map_eq_swap_mul_swap hn5 η hη hker.le (by rw [hker]; exact h.center_isPGroup)
    (by rw [hker]; exact h.center_ne_bot) hf hηk hk2

end CFSG.ComponentClassification.HarrisLit.N36
