module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34MSideComp

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem L34MSide.isPGroup_zpowers_of_pow_three {x : Y} (hx : x ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)

omit [Finite Y] in
theorem L34MSide.central_conj {L : Subgroup Y} {x : Y} (hx : ∀ l ∈ L, x * l = l * x) (n : Y) :
    ∀ l ∈ L.map (MulAut.conj n).toMonoidHom, n * x * n⁻¹ * l = l * (n * x * n⁻¹) := by
  intro l hl
  obtain ⟨l₀, hl₀, rfl⟩ := hl
  have e := hx l₀ hl₀
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc n * x * n⁻¹ * (n * l₀ * n⁻¹) = n * (x * l₀) * n⁻¹ := by group
    _ = n * (l₀ * x) * n⁻¹ := by rw [e]
    _ = n * l₀ * n⁻¹ * (n * x * n⁻¹) := by group

omit [Finite Y] in
theorem L34MSide.central_of_conj {L : Subgroup Y} {x n : Y}
    (hx : ∀ l ∈ L.map (MulAut.conj n).toMonoidHom, x * l = l * x) :
    ∀ l ∈ L, n⁻¹ * x * n * l = l * (n⁻¹ * x * n) := by
  intro l hl
  have e := hx _ (conj_mem_map_conj n hl)
  calc n⁻¹ * x * n * l = n⁻¹ * (x * (n * l * n⁻¹)) * n := by group
    _ = n⁻¹ * ((n * l * n⁻¹) * x) * n := by rw [e]
    _ = l * (n⁻¹ * x * n) := by group

theorem L34MSide.uniq_of_le {z : Y} {R T : Subgroup Y}
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hRgen : ∀ r ∈ R, ∃ t ∈ T, ∃ i : ℕ, r = t * z ^ i)
    (hRp : IsPGroup 3 R)
    (hRsyl : ∀ Q : Subgroup Y, Q ≤ Subgroup.centralizer ({z} : Set Y) → IsPGroup 3 Q →
      Nat.card Q ≤ Nat.card R)
    (hRC : R ≤ Subgroup.centralizer ({z} : Set Y))
    (hfus : ∀ r ∈ R, r ∉ T → ∃ n : Y, n * r * n⁻¹ ∈ Subgroup.zpowers z)
    (hzcomp : ∀ L : Subgroup Y, IsComponentOf L ⊤ → z ∉ Subgroup.centralizer (L : Set Y))
    (hW : ∀ L : Subgroup Y, IsComponentOf L ⊤ → ∃ w ∈ L, w ≠ 1 ∧
      IsPGroup 3 (Subgroup.zpowers w) ∧ w * z = z * w)
    {L₀ : Subgroup Y} (hL₀ : IsComponentOf L₀ ⊤) (hTL₀ : T ≤ L₀)
    (hTnc : ∀ t ∈ T, t ≠ 1 → ∃ l ∈ L₀, t * l ≠ l * t) :
    ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = L₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm_ne : ∀ {A B : Subgroup Y}, IsComponentOf A ⊤ → IsComponentOf B ⊤ → A ≠ B →
      ∀ {x : Y}, x ∈ B → ∀ l ∈ A, x * l = l * x :=
    fun hA hB hne _ hx => L34MSide.comm_of_mem_two hA hB hne hx
  intro L'' hL''
  by_contra hne
  obtain ⟨w, hwL, hw1, hwp, hwz⟩ := hW L'' hL''
  have hwR : ∀ r ∈ R, w * r = r * w := by
    intro r hr
    obtain ⟨t, ht, i, rfl⟩ := hRgen r hr
    have hwt : w * t = t * w := (hcomm_ne hL'' hL₀ hne (hTL₀ ht) w hwL).symm
    have hwzi : w * z ^ i = z ^ i * w := (Commute.pow_right hwz i).eq
    calc w * (t * z ^ i) = (w * t) * z ^ i := by group
      _ = t * (w * z ^ i) := by rw [hwt]; group
      _ = t * (z ^ i * w) := by rw [hwzi]
      _ = t * z ^ i * w := by group
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (R : Set Y) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (R : Set Y))
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro r hr
    exact (hwR r hr).symm
  have hsup : IsPGroup 3 ↥((Subgroup.zpowers w) ⊔ R) := hwp.to_sup_of_normal_right' hRp hwN
  have hsupC : (Subgroup.zpowers w) ⊔ R ≤ Subgroup.centralizer ({z} : Set Y) := by
    refine sup_le ?_ hRC
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hwz
  have hle := hRsyl _ hsupC hsup
  have heq : (Subgroup.zpowers w) ⊔ R = R :=
    (Subgroup.eq_of_le_of_card_ge le_sup_right hle).symm
  have hwRm : w ∈ R := heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers w)
  have hwT : w ∉ T := by
    intro hwT
    obtain ⟨l, hl, hne'⟩ := hTnc w hwT hw1
    exact hne' (hcomm_ne hL₀ hL'' (Ne.symm hne) hwL l hl)
  obtain ⟨n, hn⟩ := hfus w hwRm hwT
  have hw1' : n * w * n⁻¹ ≠ 1 := by
    intro h
    apply hw1
    have := congrArg (fun v => n⁻¹ * v * n) h
    simpa [mul_assoc] using this
  have hz4 : z ∈ L''.map (MulAut.conj n).toMonoidHom :=
    (Subgroup.zpowers_le.mpr (conj_mem_map_conj n hwL))
      (L34MSide.mem_zpowers_of_mem_zpowers hz3 hz1 hn hw1')
  have h4 : IsComponentOf (L''.map (MulAut.conj n).toMonoidHom) ⊤ :=
    isComponentOf_map_conj hL'' n
  have e1 : L''.map (MulAut.conj n).toMonoidHom = L₀ := by
    by_contra h
    apply hzcomp L₀ hL₀
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (hcomm_ne hL₀ h4 (Ne.symm h) hz4 l hl).symm
  have e2 : L''.map (MulAut.conj n).toMonoidHom = L'' := by
    by_contra h
    apply hzcomp L'' hL''
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (hcomm_ne hL'' h4 (Ne.symm h) hz4 l hl).symm
  exact hne (e2.symm.trans e1)

theorem L34MSide.exists_unique_component_le_good {z : Y} {R T : Subgroup Y} (S : Sylow 3 Y)
    (hcore : primeComplementCore (G := Y) 3 = ⊥)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hRgen : ∀ r ∈ R, ∃ t ∈ T, ∃ i : ℕ, r = t * z ^ i)
    (hRp : IsPGroup 3 R)
    (hRsyl : ∀ Q : Subgroup Y, Q ≤ Subgroup.centralizer ({z} : Set Y) → IsPGroup 3 Q →
      Nat.card Q ≤ Nat.card R)
    (hRC : R ≤ Subgroup.centralizer ({z} : Set Y))
    (hconj : ∀ y ∈ Subgroup.centralizer ({z} : Set Y), IsPGroup 3 (Subgroup.zpowers y) →
      ∃ c ∈ Subgroup.centralizer ({z} : Set Y), c⁻¹ * y * c ∈ R)
    (hfus : ∀ r ∈ R, r ∉ T → ∃ n : Y, n * r * n⁻¹ ∈ Subgroup.zpowers z)
    (htr : ∀ t ∈ T, t ≠ 1 → ∀ s ∈ T, s ≠ 1 → ∃ n : Y, n * t * n⁻¹ = s)
    (hcenter : ∀ x ∈ (S : Subgroup Y), (∀ y ∈ (S : Subgroup Y), x * y = y * x) → x ∈ T)
    (hzcomp : ∀ L : Subgroup Y, IsComponentOf L ⊤ → z ∉ Subgroup.centralizer (L : Set Y))
    (hW : ∀ L : Subgroup Y, IsComponentOf L ⊤ → ∃ w ∈ L, w ≠ 1 ∧
      IsPGroup 3 (Subgroup.zpowers w) ∧ w * z = z * w)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) {y : Y} (hyL : y ∈ L)
    (hyp : IsPGroup 3 (Subgroup.zpowers y)) (hyz : y * z = z * y)
    (hync : ∃ l ∈ L, y * l ≠ l * y)
    (hcenT : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L.Normal → T ≤ L →
      ¬ ∀ t ∈ T, ∀ l ∈ L, t * l = l * t) :
    ∃ L₀ : Subgroup Y, IsComponentOf L₀ ⊤ ∧ L₀.Normal ∧ T ≤ L₀ ∧
      (∀ t ∈ T, t ≠ 1 → ∃ l ∈ L₀, t * l ≠ l * t) ∧
      (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = L₀) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyC : y ∈ Subgroup.centralizer ({z} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyz
  obtain ⟨c, -, hcR⟩ := hconj y hyC hyp
  set y' := c⁻¹ * y * c with hy'
  set Lc := L.map (MulAut.conj c⁻¹).toMonoidHom with hLcdef
  have hLc : IsComponentOf Lc ⊤ := isComponentOf_map_conj hL c⁻¹
  have hy'L : y' ∈ Lc := by
    have := conj_mem_map_conj c⁻¹ hyL
    rw [inv_inv] at this
    exact this
  have hy'nc : ∃ l ∈ Lc, y' * l ≠ l * y' := by
    have := L34MSide.noncentral_conj hync c⁻¹
    simp only [inv_inv] at this
    exact this
  have hy'1 : y' ≠ 1 := L34MSide.ne_one_of_noncentral hy'nc
  by_cases hy'T : y' ∈ T
  ·
    have hcomm_ne : ∀ {A B : Subgroup Y}, IsComponentOf A ⊤ → IsComponentOf B ⊤ → A ≠ B →
        ∀ {x : Y}, x ∈ B → ∀ l ∈ A, x * l = l * x :=
      fun hA hB hne _ hx => L34MSide.comm_of_mem_two hA hB hne hx
    have hconjT : ∀ s ∈ T, s ≠ 1 → ∃ n : Y, s ∈ Lc.map (MulAut.conj n).toMonoidHom ∧
        ∃ l ∈ Lc.map (MulAut.conj n).toMonoidHom, s * l ≠ l * s := by
      intro s hs hs1
      obtain ⟨n, hn⟩ := htr y' hy'T hy'1 s hs hs1
      refine ⟨n, hn ▸ conj_mem_map_conj n hy'L, ?_⟩
      rw [← hn]
      exact L34MSide.noncentral_conj hy'nc n
    have hTLc : T ≤ Lc := by
      intro s hs
      by_cases hs1 : s = 1
      · rw [hs1]; exact Lc.one_mem
      obtain ⟨n, hsB, hsnc⟩ := hconjT s hs hs1
      set B := Lc.map (MulAut.conj n).toMonoidHom with hBdef
      have hB : IsComponentOf B ⊤ := isComponentOf_map_conj hLc n
      by_cases hBe : B = Lc
      · rw [← hBe]; exact hsB
      by_cases hsz : s ∈ Subgroup.zpowers y'
      · exact (Subgroup.zpowers_le.mpr hy'L) hsz
      have hts : y' * s ∈ T := T.mul_mem hy'T hs
      have hts1 : y' * s ≠ 1 := by
        intro h
        apply hsz
        have : s = y'⁻¹ := by
          calc s = y'⁻¹ * (y' * s) := by group
            _ = y'⁻¹ := by rw [h, mul_one]
        rw [this]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers y')
      obtain ⟨n', htsC, htsnc⟩ := hconjT (y' * s) hts hts1
      set C := Lc.map (MulAut.conj n').toMonoidHom with hCdef
      have hC : IsComponentOf C ⊤ := isComponentOf_map_conj hLc n'
      by_cases hCe : C = Lc
      · have h1 : y' * s ∈ Lc := hCe ▸ htsC
        have : s = y'⁻¹ * (y' * s) := by group
        rw [this]
        exact Lc.mul_mem (Lc.inv_mem hy'L) h1
      exfalso
      by_cases hCB : C = B
      ·
        have h1 : y' * s ∈ B := hCB ▸ htsC
        have hy'B : y' ∈ B := by
          have : y' = (y' * s) * s⁻¹ := by group
          rw [this]
          exact B.mul_mem h1 (B.inv_mem hsB)
        obtain ⟨l, hl, hne⟩ := hy'nc
        exact hne (hcomm_ne hLc hB (Ne.symm hBe) hy'B l hl)
      ·
        obtain ⟨l, hl, hne⟩ := hy'nc
        apply hne
        have e1 := hcomm_ne hLc hC (Ne.symm hCe) htsC l hl
        have e2 := hcomm_ne hLc hB (Ne.symm hBe) hsB l hl
        calc y' * l = (y' * s) * (s⁻¹ * l) := by group
          _ = (y' * s) * (l * s⁻¹) := by
              congr 1
              calc s⁻¹ * l = s⁻¹ * (l * s) * s⁻¹ := by group
                _ = s⁻¹ * (s * l) * s⁻¹ := by rw [e2]
                _ = l * s⁻¹ := by group
          _ = l * (y' * s) * s⁻¹ := by rw [← mul_assoc, e1]
          _ = l * y' := by group
    have hTnc : ∀ t ∈ T, t ≠ 1 → ∃ l ∈ Lc, t * l ≠ l * t := by
      intro t ht ht1
      obtain ⟨n, htB, htnc⟩ := hconjT t ht ht1
      have hB : IsComponentOf (Lc.map (MulAut.conj n).toMonoidHom) ⊤ :=
        isComponentOf_map_conj hLc n
      by_cases hBe : Lc.map (MulAut.conj n).toMonoidHom = Lc
      · rw [← hBe]; exact htnc
      exfalso
      obtain ⟨l, hl, hne⟩ := htnc
      exact hne (hcomm_ne hB hLc hBe (hTLc ht) l hl)
    have huniq := L34MSide.uniq_of_le hz3 hz1 hRgen hRp hRsyl hRC hfus hzcomp hW hLc hTLc hTnc
    exact ⟨Lc, hLc, L34MSide.normal_of_unique hLc huniq, hTLc, hTnc, huniq⟩
  ·
    obtain ⟨n, hn⟩ := hfus y' hcR hy'T
    set L₀ := Lc.map (MulAut.conj n).toMonoidHom with hL₀def
    have hL₀ : IsComponentOf L₀ ⊤ := isComponentOf_map_conj hLc n
    have hw1 : n * y' * n⁻¹ ≠ 1 := by
      intro h
      apply hy'1
      have := congrArg (fun v => n⁻¹ * v * n) h
      simpa [mul_assoc] using this
    have hzL₀ : z ∈ L₀ :=
      (Subgroup.zpowers_le.mpr (conj_mem_map_conj n hy'L))
        (L34MSide.mem_zpowers_of_mem_zpowers hz3 hz1 hn hw1)
    obtain ⟨huniq, hnorm⟩ := L34MSide.unique_normal_of_mem hzcomp hL₀ hzL₀
    have hTL₀ : T ≤ L₀ := L34MSide.le_of_normal_of_three_dvd S hcenter htr hnorm
      (L34MSide.three_dvd_card_component hcore hL₀)
    refine ⟨L₀, hL₀, hnorm, hTL₀, ?_, huniq⟩
    intro t ht ht1
    by_contra hc
    push Not at hc
    apply hcenT L₀ hL₀ hnorm hTL₀
    intro s hs
    by_cases hs1 : s = 1
    · intro l _; rw [hs1]; group
    obtain ⟨m, hm⟩ := htr t ht ht1 s hs hs1
    rw [← hm]
    exact L34MSide.conj_comm_of_normal hnorm hc m

end CFSG.AGLEmbedding
