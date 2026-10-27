module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Inner
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique.Setup.Family

abbrev S23 : Type := ↥NativeSporadic.M23

section Facts

theorem m23_card_eq : Nat.card S23 = 2 ^ 7 * 79695 := by
  rw [m23_card]
  norm_num

theorem m23_conj_into_R
    (B : Subgroup S23) (hB : ∀ x ∈ B, x * x = 1) :
    ∃ g : S23, ∀ x ∈ B, g * x * g⁻¹ ∈ m23rl := by
  obtain ⟨hlen, hnd, h1, hmul, hpow⟩ := m23_sylow_check
  exact exists_conj_mem_list m23rl h1 hmul hpow hnd hlen m23_card_eq (by decide) B hB

theorem m23_rank_le
    : ∀ B : Subgroup S23, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
    (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 4 := by
  intro B hcomm hsq
  by_contra hgt
  push Not at hgt
  obtain ⟨g, hg⟩ := m23_conj_into_R B hsq
  set B' : Subgroup S23 := B.map (MulAut.conj g).toMonoidHom with hB'
  have hmem : ∀ x ∈ B', x ∈ m23rl := by
    rintro _ ⟨y, hy, rfl⟩
    exact hg y hy
  have hcomm' : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hcomm a ha b hb]
      _ = _ := by group
  have hsq' : ∀ x ∈ B', x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    show g * a * g⁻¹ * (g * a * g⁻¹) = 1
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [hsq a ha]; group
  have hcard : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  obtain ⟨l, hl, hlen, hlB⟩ := exists_indepList_of_lt_card B' hcomm' hsq' 4 (by rw [hcard]; exact hgt)
  have hl' : ∀ y ∈ l, y ∈ m23rinv := by
    intro y hy
    have h1 : y ∈ m23rl := hmem y (hlB y hy)
    rw [m23rinv, invList, List.mem_filter]
    exact ⟨h1, by simpa using ⟨hl.ne_one y hy, hsq' y (hlB y hy)⟩⟩
  have := forallIndep_sound m23rinv (fun _ => false) 5 [] m23_rank_check l hlen hl'
    (by simpa using hl)
  simp at this

theorem m23_gen1
    (B : Subgroup S23) (hsq : ∀ x ∈ B, x * x = 1) (hne : B ≠ ⊥) :
    ∃ cs : List S23, cs.length = 3 ∧
      ∃ x ∈ Subgroup.closure (conjSet cs (B : Set S23)), orderOf x = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := m23_conj_into_R B hsq
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  set b' : S23 := g * b * g⁻¹ with hb'
  have hb'mem : b' ∈ m23rl := hg b hbB
  have hb'ne : b' ≠ 1 := fun h => hb1' (conj_eq_one_iff.1 h)
  have hb'sq : b' * b' = 1 := by
    calc b' * b' = g * (b * b) * g⁻¹ := by rw [hb']; group
      _ = 1 := by rw [hsq b hbB]; group
  have hinv : b' ∈ m23rinv := by
    rw [m23rinv, invList, List.mem_filter]
    exact ⟨hb'mem, by simpa using ⟨hb'ne, hb'sq⟩⟩
  obtain ⟨hok, hcover⟩ := m23_G1_check
  obtain ⟨e, he, hanyr⟩ := List.any_eq_true.1 (List.all_eq_true.1 hcover b' hinv)
  obtain ⟨r, -, hr⟩ := List.any_eq_true.1 hanyr
  have hr' : r * b' * r⁻¹ = m23rl.getD e.1 1 := beq_iff_eq.1 hr
  have hew := List.all_eq_true.1 hok e he
  simp only [Bool.and_eq_true] at hew
  obtain ⟨hlen, hw⟩ := hew
  obtain ⟨cs0, hcs0, x, hx, hxp⟩ := exists_gen_of_witOK [m23rl.getD e.1 1] (m23conj e.2.1) e.2.2
    (p := 11) hw
  have hlen' : e.2.1.length = 2 := by simpa using hlen
  have hx' := closure_conjSet_transfer (T := ({b} : Set S23)) (r * g)
    (fun t' ht' => ⟨b, rfl, by
      have : t' = m23rl.getD e.1 1 := by simpa using ht'
      rw [this, ← hr', hb']; group⟩) cs0 hx
  refine ⟨cs0.map (· * (r * g)), by simpa [m23conj, hlen'] using hcs0, x, ?_, hxp⟩
  exact Subgroup.closure_mono (conjSet_mono (by simpa using hbB)) hx'

theorem m23_gen2
    (B : Subgroup S23) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) (h4 : 4 ≤ Nat.card B) :
    ∃ cs : List S23, cs.length = 2 ∧
      ∃ x ∈ Subgroup.closure (conjSet cs (B : Set S23)), orderOf x = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := m23_conj_into_R B hsq
  obtain ⟨l, hl, hlen, hlB⟩ := exists_indepList_of_lt_card B hcomm hsq 1 (by omega)
  obtain ⟨x, y, rfl⟩ : ∃ x y, l = [x, y] := by
    match l, hlen with
    | [x, y], _ => exact ⟨x, y, rfl⟩
  obtain ⟨hx2, hy2, hx1, hy1, hxy, hxne⟩ := indepList_two hl
  have hxB : x ∈ B := hlB x (by simp)
  have hyB : y ∈ B := hlB y (by simp)
  set x' : S23 := g * x * g⁻¹ with hx'
  set y' : S23 := g * y * g⁻¹ with hy'
  have hsqc : ∀ z : S23, z * z = 1 → (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := fun z hz => by
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz]; group
  have hx'inv : x' ∈ m23rinv := by
    rw [m23rinv, invList, List.mem_filter]
    exact ⟨hg x hxB, by simpa using ⟨fun h => hx1 (conj_eq_one_iff.1 h), hsqc x hx2⟩⟩
  have hy'inv : y' ∈ m23rinv := by
    rw [m23rinv, invList, List.mem_filter]
    exact ⟨hg y hyB, by simpa using ⟨fun h => hy1 (conj_eq_one_iff.1 h), hsqc y hy2⟩⟩
  have hne' : x' ≠ y' := fun h => hxne (by simpa [hx', hy'] using h)
  have hcomm' : x' * y' = y' * x' := by
    calc x' * y' = g * (x * y) * g⁻¹ := by rw [hx', hy']; group
      _ = g * (y * x) * g⁻¹ := by rw [hxy]
      _ = y' * x' := by rw [hx', hy']; group
  have hpair : (x', y') ∈ pairList NativeSporadic.M23 m23rinv := by
    rw [pairList, List.mem_flatMap]
    refine ⟨x', hx'inv, ?_⟩
    rw [List.mem_filterMap]
    exact ⟨y', hy'inv, by simp [hne', hcomm']⟩
  obtain ⟨hok, hcover⟩ := m23_G2_check
  obtain ⟨e, he, hanyr⟩ := List.any_eq_true.1 (List.all_eq_true.1 hcover _ hpair)
  obtain ⟨r, -, hr⟩ := List.any_eq_true.1 hanyr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨hr1, hr2⟩ := hr
  have hr1' : r * x' * r⁻¹ = m23rl.getD e.1 1 := beq_iff_eq.1 hr1
  have hr2' : r * y' * r⁻¹ = m23rl.getD e.2.1 1 := beq_iff_eq.1 hr2
  have hew := List.all_eq_true.1 hok e he
  simp only [Bool.and_eq_true] at hew
  obtain ⟨hlen, hw⟩ := hew
  obtain ⟨cs0, hcs0, z, hz, hzp⟩ := exists_gen_of_witOK [m23rl.getD e.1 1, m23rl.getD e.2.1 1]
    (m23conj e.2.2.1) e.2.2.2 (p := 11) hw
  have hlen' : e.2.2.1.length = 1 := by simpa using hlen
  have hz' := closure_conjSet_transfer (T := ({x, y} : Set S23)) (r * g)
    (fun t' ht' => by
      have : t' = m23rl.getD e.1 1 ∨ t' = m23rl.getD e.2.1 1 := by simpa using ht'
      rcases this with rfl | rfl
      · exact ⟨x, by simp, by rw [← hr1', hx']; group⟩
      · exact ⟨y, by simp, by rw [← hr2', hy']; group⟩) cs0 hz
  refine ⟨cs0.map (· * (r * g)), by simpa [m23conj, hlen'] using hcs0, z, ?_, hzp⟩
  refine Subgroup.closure_mono (conjSet_mono ?_) hz'
  intro t ht
  rcases ht with rfl | rfl
  · exact hxB
  · exact hyB

end Facts

theorem m23_autInner
    : ∀ φ : S23 ≃* S23, ∃ s : S23, ∀ x, φ x = s * x * s⁻¹ :=
  autInner_of_card_le m23_center_eq_bot' m23_mulAut_card

theorem m23_weight_lt
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L) (hirr : IsIrrOn L)
    (e : CQ L ≃* NativeSporadic.Carrier .M23)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  have e' : CQ L ≃* S23 := e
  have hEL : E ≤ L := le_of_autInner hW hq.1 hirr hE hEel e' m23_autInner
  have hcard : Nat.card E ≤ 2 ^ 4 := card_le_two_pow_of_le hW hirr hEL hEel e' m23_rank_le
  have hBcomm := imgSub_comm (hEL := hEL) (e := e') hEel
  have hBsq := imgSub_sq (hEL := hEL) (e := e') hEel
  have hBcard := card_imgSub hW hirr hEL hEel e'
  have hidx := index_fixV_eq_two_pow hW E
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  apply weight_lt_of_lt_index
  by_cases h8 : Nat.card E ≤ 8
  · have hne : imgSub L E hEL e' ≠ ⊥ := by
      intro h
      have h1 : Nat.card (imgSub L E hEL e') = 1 := by rw [h]; simp
      rw [hBcard] at h1
      exact hEne (Subgroup.card_eq_one.1 h1)
    obtain ⟨cs, hcs, hx⟩ := m23_gen1 _ hBsq hne
    have h := two_pow_le_of_inner_gen hW hEL e' (k := 3) (p := 11) (by norm_num) ⟨cs, hcs, hx⟩
    rw [orderOf_two_zmod_11] at h
    have h2 := two_pow_le_of_pow_le hidx h (ρ := 4) (by norm_num)
    omega
  · have h4 : 4 ≤ Nat.card (imgSub L E hEL e') := by rw [hBcard]; omega
    obtain ⟨cs, hcs, hx⟩ := m23_gen2 _ hBcomm hBsq h4
    have h := two_pow_le_of_inner_gen hW hEL e' (k := 2) (p := 11) (by norm_num) ⟨cs, hcs, hx⟩
    rw [orderOf_two_zmod_11] at h
    have h2 := two_pow_le_of_pow_le hidx h (ρ := 5) (by norm_num)
    omega

theorem sporadicExclusion_M23
    : SporadicExclusion .M23 := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel _
  exact m23_weight_lt hW hq hirr e hE hEne hEel

end CFSG.QuasithinUnique.Setup.X1
