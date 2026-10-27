module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneSwapIPair
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneSwapIInner
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneSwapRoot

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

omit [Finite G] in
theorem notMem_normalizer_swapComponent {s : EscapingQuotient z}
    (hs : s ∉ Subgroup.normalizer (J : Set (EscapingQuotient z))) :
    s ∉ Subgroup.normalizer ((swapComponent J s : Subgroup _) : Set (EscapingQuotient z)) := by
  intro h1
  apply hs
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 ⊢
  exact Subgroup.map_injective (MulAut.conj s).injective h1

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) {s : EscapingQuotient z}
  (hsS : s ∈ escapingSylowImage S z)
  (hs : s ∉ Subgroup.normalizer (J : Set (EscapingQuotient z)))
include h hsS hs

theorem mem_sup_of_mul_self_eq_one
    {x : EscapingQuotient z} (hxS : x ∈ escapingSylowImage S z)
    (hx2 : x * x = 1) : x ∈ J ⊔ swapComponent J s := by
  have hq := h.quotientData
  have h' := h.swap_setting hsS
  have hxN := h.mem_normalizer_of_mul_self_eq_one hs hxS hx2
  have hxN' := h'.mem_normalizer_of_mul_self_eq_one (notMem_normalizer_swapComponent hs) hxS hx2
  obtain ⟨q, hqS, hqJ, c, -, hcK, hqc⟩ := h.exists_mul_eq_of_mul_self_eq_one hxS hxN hx2
  obtain ⟨q', -, hq'J, c', hc'S, hc'K, hqc'⟩ :=
    h'.exists_mul_eq_of_mul_self_eq_one hxS hxN' hx2
  have hJJ := h.swap_le_centralizer hs
  have hJJ' := h.le_centralizer_swap hs
  have hqq' : Commute q q' := Subgroup.mem_centralizer_iff.mp (hJJ hq'J) q hqJ
  have hk : q⁻¹ * c' = q'⁻¹ * c := by
    have e1 : c' = q'⁻¹ * x := by rw [← hqc', inv_mul_cancel_left]
    have e2 : c = q⁻¹ * x := by rw [← hqc, inv_mul_cancel_left]
    rw [e1, e2, ← mul_assoc, ← mul_assoc, hqq'.inv_inv.eq]
  have hkS : q⁻¹ * c' ∈ escapingSylowImage S z :=
    (escapingSylowImage S z).mul_mem ((escapingSylowImage S z).inv_mem hqS) hc'S
  have hkK : q⁻¹ * c' ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
    rw [hk]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hJJ hq'J)) hcK
  have hkK' : q⁻¹ * c' ∈
      Subgroup.centralizer ((swapComponent J s : Subgroup _) : Set (EscapingQuotient z)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hJJ' hqJ)) hc'K
  have hk1 : q⁻¹ * c' = 1 ∨ q⁻¹ * c' = escapingBar z := by
    by_contra hne
    push Not at hne
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp h.sylowImage_isPGroup) ⟨_, hkS⟩
    rw [Subgroup.orderOf_mk] at hm
    obtain ⟨n, hn⟩ := exists_pow_sq_eq_of_unique
      (L := escapingSylowImage S z ⊓ Subgroup.centralizer (J : Set (EscapingQuotient z)))
      (fun y hy hy2 => h.eq_bar_of_mem_centralizer hy.1 hy.2 hy2) ⟨hkS, hkK⟩ hm hne.1 hne.2
    set k₁ := (q⁻¹ * c') ^ n with hk₁
    obtain ⟨a, haS, haJ, ha2⟩ := h.exists_sq_eq_bar h.component
    have hk₁K : k₁ ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) :=
      Subgroup.pow_mem _ hkK n
    have hk₁a : Commute k₁ a := (Subgroup.mem_centralizer_iff.mp hk₁K a haJ).symm
    have he2 : (k₁ * a) ^ 2 = 1 := by rw [hk₁a.mul_pow, hn, ha2, ← pow_two, h.bar_sq]
    have haC : a ∉ Subgroup.centralizer (J : Set (EscapingQuotient z)) := fun haC => by
      obtain ⟨h1, h2⟩ := h.ne_of_sq_eq_bar ha2
      rcases h.eq_of_mem_centralizer_component h.component haJ haC with h3 | h3
      · exact h1 h3
      · exact h2 h3
    have hk₁inv : k₁⁻¹ ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) :=
      Subgroup.inv_mem _ hk₁K
    have he1 : k₁ * a ≠ 1 := fun h1 => haC (by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact hk₁inv)
    have hez : k₁ * a ≠ escapingBar z := fun h1 => haC (by
      rw [show a = k₁⁻¹ * escapingBar z by rw [← h1, inv_mul_cancel_left]]
      exact Subgroup.mul_mem _ hk₁inv hq.bar_mem_component_centralizer)
    exact hez (h'.eq_bar_of_mem_centralizer
      ((escapingSylowImage S z).mul_mem ((escapingSylowImage S z).pow_mem hkS n) haS)
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ hkK' n) (hJJ' haJ)) (orderOf_eq_prime he2 he1))
  have hx : x = q' * (q * (q⁻¹ * c')) := by rw [mul_inv_cancel_left, hqc']
  rw [hx]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right hq'J)
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left hqJ) ?_)
  rcases hk1 with h1 | h1 <;> rw [h1]
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_sup_left (h.square.caseTwo J h.component)

theorem sq_eq_of_mem_normalizer_sup
    {t : EscapingQuotient z} (htS : t ∈ escapingSylowImage S z)
    (htN : t ∈ Subgroup.normalizer (J : Set (EscapingQuotient z)))
    (htJJ : t ∈ J ⊔ swapComponent J s) : t ^ 2 = 1 ∨ t ^ 2 = escapingBar z := by
  obtain ⟨c, hcS, hcJ, c', hc'S, hc'J', rfl⟩ :=
    h.exists_mul_eq_of_mem_normalizer_sup hs htS htN htJJ
  have hcc' : Commute c c' :=
    Subgroup.mem_centralizer_iff.mp (h.swap_le_centralizer hs hc'J') c hcJ
  rw [hcc'.mul_pow]
  rcases h.sq_eq_of_mem_sylowImage_inf hcS hcJ with h1 | h1 <;>
    rcases (h.swap_setting hsS).sq_eq_of_mem_sylowImage_inf hc'S hc'J' with h2 | h2 <;>
    rw [h1, h2]
  · exact Or.inl (mul_one 1)
  · exact Or.inr (one_mul _)
  · exact Or.inr (mul_one _)
  · exact Or.inl (by rw [← pow_two, h.bar_sq])

theorem sq_mul_eq_of_mul_self_eq_one
    {x y : EscapingQuotient z}
    (hxS : x ∈ escapingSylowImage S z) (hyS : y ∈ escapingSylowImage S z)
    (hx2 : x * x = 1) (hy2 : y * y = 1) : (x * y) ^ 2 = 1 ∨ (x * y) ^ 2 = escapingBar z :=
  h.sq_eq_of_mem_normalizer_sup hsS hs ((escapingSylowImage S z).mul_mem hxS hyS)
    (Subgroup.mul_mem _ (h.mem_normalizer_of_mul_self_eq_one hs hxS hx2)
      (h.mem_normalizer_of_mul_self_eq_one hs hyS hy2))
    (Subgroup.mul_mem _ (h.mem_sup_of_mul_self_eq_one hsS hs hxS hx2)
      (h.mem_sup_of_mul_self_eq_one hsS hs hyS hy2))

theorem exists_involution_pair
    {t : EscapingQuotient z} (htS : t ∈ escapingSylowImage S z)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htz : t ≠ escapingBar z) :
    ∃ i₁ ∈ escapingSylowImage S z, ∃ i₂ ∈ escapingSylowImage S z, i₁ * i₁ = 1 ∧ i₂ * i₂ = 1 ∧
      Commute i₁ t ∧ Commute i₂ t ∧ (i₁ * i₂) ^ 2 = escapingBar z := by
  have h' := h.swap_setting hsS
  have htN := h.mem_normalizer_of_mul_self_eq_one hs htS ht2
  obtain ⟨c, hcS, hcJ, c', hc'S, hc'J', rfl⟩ := h.exists_mul_eq_of_mem_normalizer_sup hs htS htN
    (h.mem_sup_of_mul_self_eq_one hsS hs htS ht2)
  have hcomm : ∀ {a a' : EscapingQuotient z}, a ∈ J → a' ∈ swapComponent J s → Commute a a' :=
    fun ha ha' => Subgroup.mem_centralizer_iff.mp (h.swap_le_centralizer hs ha') _ ha
  have hcc' : Commute c c' := hcomm hcJ hc'J'
  have hzz : escapingBar z * escapingBar z = 1 := by rw [← pow_two, h.bar_sq]
  have hsq : c ^ 2 * c' ^ 2 = 1 := by rw [← hcc'.mul_pow, pow_two, ht2]
  have hc2 : c ^ 2 = escapingBar z := by
    rcases h.sq_eq_of_mem_sylowImage_inf hcS hcJ with h1 | h1
    · exfalso
      rw [h1, one_mul] at hsq
      rcases h.eq_one_or_eq_bar_of_sq_eq_one hcJ h1 with rfl | rfl <;>
        rcases h'.eq_one_or_eq_bar_of_sq_eq_one hc'J' hsq with rfl | rfl
      · exact ht1 (mul_one 1)
      · exact htz (one_mul _)
      · exact htz (mul_one _)
      · exact ht1 hzz
    · exact h1
  have hc'2 : c' ^ 2 = escapingBar z := by
    rw [hc2] at hsq
    calc c' ^ 2 = escapingBar z * (escapingBar z * c' ^ 2) := by
          rw [← mul_assoc, hzz, one_mul]
      _ = escapingBar z := by rw [hsq, mul_one]
  obtain ⟨b, hbS, hbJ, hbc, hb2⟩ := h.exists_inv_conj_of_sq_eq_bar hcS hcJ hc2
  obtain ⟨b', hb'S, hb'J', hb'c', hb'2⟩ := h'.exists_inv_conj_of_sq_eq_bar hc'S hc'J' hc'2
  obtain ⟨hi₁, hi₂, hi₁t, hi₂t, hi⟩ := involution_pair_identities hzz hbc hb'c'
    (by rw [← pow_two, hb2]) (by rw [← pow_two, hb'2]) (by rw [← pow_two, hc2])
    (hcomm hbJ hb'J') (hcomm hbJ hc'J') (hcomm hcJ hb'J') hcc' ht2
  exact ⟨b * b', (escapingSylowImage S z).mul_mem hbS hb'S, b * b' * c,
    (escapingSylowImage S z).mul_mem ((escapingSylowImage S z).mul_mem hbS hb'S) hcS,
    hi₁, hi₂, hi₁t, hi₂t, hi⟩

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
