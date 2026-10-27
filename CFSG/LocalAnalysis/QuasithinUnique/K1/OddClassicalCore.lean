module

public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionQuotient
public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.RankOneRecog

variable {G : Type} [Group G] [Finite G]

section Isolated

omit [Finite G] in
theorem isPGroup_two_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : IsPGroup 2 (Subgroup.closure ({a, b} : Set G)) := by
  have hcomm : IsMulCommutative (Subgroup.closure ({a, b} : Set G)) :=
    Subgroup.isMulCommutative_closure (fun x hx y hy _ => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact hab
      · exact hab.symm
      · rfl)
  have key : ∀ x ∈ Subgroup.closure ({a, b} : Set G), x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    | one => simp
    | mul x y hx hy hx2 hy2 =>
      have hxy : x * y = y * x :=
        congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : Subgroup.closure ({a, b} : Set G)) ⟨y, hy⟩)
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx2, hy2, one_mul]
    | inv x _ hx2 =>
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [hx2, inv_one]
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  have := key x.1 x.2
  simpa [pow_one, sq] using this

theorem isolated_of_closed {J Q : Subgroup G} (hQ : IsSylowTwoOf Q J) {t : G} (htJ : t ∈ J)
    (ht2 : t * t = 1) (hwc : ∀ g ∈ J, g⁻¹ * t * g ∈ Q → g⁻¹ * t * g = t) :
    ∀ g ∈ J, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
  intro g hg hcomm
  set y := g * t * g⁻¹ with hy
  have hy2 : y * y = 1 := by
    calc y * y = g * (t * t) * g⁻¹ := by simp only [hy]; group
      _ = 1 := by rw [ht2]; group
  have hyJ : y ∈ J := J.mul_mem (J.mul_mem hg htJ) (J.inv_mem hg)
  have hE : IsPGroup 2 (Subgroup.closure ({t, y} : Set G)) :=
    isPGroup_two_closure_pair ht2 hy2 hcomm.symm
  have hEJ : Subgroup.closure ({t, y} : Set G) ≤ J := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact htJ
    · exact hyJ
  obtain ⟨m, hmJ, hm⟩ :=
    EscapingLocal.exists_conj_mem_of_isPGroup hQ.1 hQ.2.1 hQ.2.2 hEJ hE
  have htc : t ∈ Subgroup.closure ({t, y} : Set G) := Subgroup.subset_closure (by simp)
  have hyc : y ∈ Subgroup.closure ({t, y} : Set G) := Subgroup.subset_closure (by simp)
  have h1 : m * t * m⁻¹ = t := by
    have := hwc m⁻¹ (J.inv_mem hmJ) (by simpa using hm t htc)
    simpa using this
  have h2 : m * y * m⁻¹ = t := by
    have hmy : m * y * m⁻¹ ∈ Q := hm y hyc
    have := hwc (m * g)⁻¹ (J.inv_mem (J.mul_mem hmJ hg))
      (by simpa [hy, mul_assoc] using hmy)
    simpa [hy, mul_assoc] using this
  have h3 : m * y * m⁻¹ = m * t * m⁻¹ := h2.trans h1.symm
  calc y = m⁻¹ * (m * y * m⁻¹) * m := by group
    _ = m⁻¹ * (m * t * m⁻¹) * m := by rw [h3]
    _ = t := by group

theorem centralizes_of_isolated {J L : Subgroup G} [L.Normal] (hLJ : L ≤ J)
    (hL : IsSimpleGroup L) (hev : 2 ∣ Nat.card L) {t : G} (htJ : t ∈ J) (ht1 : t ≠ 1)
    (ht2 : t * t = 1)
    (hiso : ∀ g ∈ J, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t) :
    t ∈ Subgroup.centralizer (L : Set G) := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  obtain ⟨N₀, hN₀n, hN₀odd, hN₀⟩ := CFSG.ZStar.glauberman_zStar J ⟨t, htJ⟩
    (fun h => ht1 (congrArg Subtype.val h)) (Subtype.ext ht2) (by
      intro g hg
      refine Subtype.ext (hiso g g.2 ?_)
      simpa using congrArg Subtype.val hg)
  let M : Subgroup G := N₀.map J.subtype
  have hMcard : Nat.card M = Nat.card N₀ := Subgroup.card_map_of_injective J.subtype_injective
  have hModd : ¬ 2 ∣ Nat.card M := by
    rw [hMcard]
    exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hN₀odd)
  have hMn : ∀ j ∈ J, ∀ m ∈ M, j * m * j⁻¹ ∈ M := by
    rintro j hj _ ⟨n, hn, rfl⟩
    exact ⟨⟨j, hj⟩ * n * ⟨j, hj⟩⁻¹, hN₀n.conj_mem n hn ⟨j, hj⟩, by simp⟩
  have hP : ((M ⊓ L).subgroupOf L).Normal := by
    refine ⟨fun x hx l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨?_, ?_⟩
    · have := hMn (l : G) (hLJ l.2) _ hx.1
      simpa using this
    · exact L.mul_mem (L.mul_mem l.2 hx.2) (L.inv_mem l.2)
  have hbot : M ⊓ L = ⊥ := by
    rcases (haveI := hP; IsSimpleGroup.eq_bot_or_eq_top_of_normal ((M ⊓ L).subgroupOf L)) with
      h | h
    · refine eq_bot_iff.mpr fun x hx => ?_
      have : (⟨x, hx.2⟩ : L) ∈ (M ⊓ L).subgroupOf L := hx
      rw [h, Subgroup.mem_bot] at this
      simpa using congrArg Subtype.val this
    · exfalso
      have hLM : L ≤ M := by
        intro x hx
        have : (⟨x, hx⟩ : L) ∈ (M ⊓ L).subgroupOf L := h ▸ Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp this).1
      exact hModd (hev.trans (Subgroup.card_dvd_of_le hLM))
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hc : l * t * l⁻¹ * t⁻¹ ∈ M := by
    have := hN₀ ⟨l, hLJ hl⟩
    exact ⟨_, this, by simp⟩
  have hcL : l * t * l⁻¹ * t⁻¹ ∈ L := by
    have h1 : t * l⁻¹ * t⁻¹ ∈ L := by
      have := Subgroup.Normal.conj_mem ‹L.Normal› l⁻¹ (L.inv_mem hl) t
      simpa using this
    simpa [mul_assoc] using L.mul_mem hl h1
  have h1 : l * t * l⁻¹ * t⁻¹ = 1 := by
    have : l * t * l⁻¹ * t⁻¹ ∈ M ⊓ L := ⟨hc, hcL⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  calc l * t = (l * t * l⁻¹ * t⁻¹) * (t * l) := by group
    _ = t * l := by rw [h1, one_mul]

end Isolated

section Closed

theorem exists_sylow_closed {R A J : Subgroup G} (hR : IsSylowTwoOf R ⊤) (hAR : A ≤ R)
    (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ R → g⁻¹ * a * g ∈ A)
    (hAJ : ∀ b ∈ A, ∀ j ∈ J, b * j * b⁻¹ ∈ J) :
    ∃ Q : Subgroup G, IsSylowTwoOf Q J ∧ A ⊓ J ≤ Q ∧
      ∀ b ∈ A ⊓ J, ∀ g ∈ J, g⁻¹ * b * g ∈ Q → g⁻¹ * b * g ∈ A ⊓ J := by
  have hA2 : IsPGroup 2 A := hR.2.1.to_le hAR
  have hAN : A ≤ Subgroup.normalizer (J : Set G) := fun b hb =>
    mem_normalizer_of_conj_mem (fun j hj => hAJ b hb j hj)
  have hMN : J ⊔ A ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hAN
  have hAM : A ≤ J ⊔ A := le_sup_right
  have hJM : J ≤ J ⊔ A := le_sup_left
  obtain ⟨R₀, hR₀, hAR₀⟩ := EscapingLocal.exists_isSylowTwoOf_ge hAM hA2
  obtain ⟨R₁, hR₁, hR₀R₁⟩ := EscapingLocal.exists_isSylowTwoOf_ge (le_top : R₀ ≤ ⊤) hR₀.2.1
  have hcl₁ := stronglyClosed_of_le_pGroup hR le_top hR₁.2.1 (hAR₀.trans hR₀R₁)
    (fun a ha g _ hg => hcl a ha g hg)
  have hJn : (J.subgroupOf (J ⊔ A)).Normal := by
    refine ⟨fun n hn m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hm := hMN m.2
    have := (Subgroup.mem_normalizer_iff.mp hm (n : G)).mp hn
    simpa using this
  have hQ : IsSylowTwoOf (R₀ ⊓ J) J :=
    isSylowTwoOf_inf_of_subnormal hR₀ hJM (Subgroup.Normal.isSubnormal hJn)
  refine ⟨R₀ ⊓ J, hQ, fun x hx => ⟨hAR₀ hx.1, hx.2⟩, ?_⟩
  intro b hb g hg hgQ
  have h1 := hcl₁ b hb.1 g (Subgroup.mem_top g) (hR₀R₁ hgQ.1)
  exact ⟨h1, J.mul_mem (J.mul_mem (J.inv_mem hg) hb.2) hg⟩

end Closed

section Burnside

omit [Finite G] in
theorem isSylowTwoOf_mono {Q M J : Subgroup G} (hQ : IsSylowTwoOf Q J) (hQM : Q ≤ M)
    (hMJ : M ≤ J) : IsSylowTwoOf Q M := by
  refine ⟨hQM, hQ.2.1, fun hd => hQ.2.2 ?_⟩
  have h := Subgroup.relIndex_mul_relIndex Q M J hQM hMJ
  exact hd.trans (Dvd.intro _ h)

theorem burnside_abelian {J Q : Subgroup G} (hQ : IsSylowTwoOf Q J)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) {x y g : G} (hxQ : x ∈ Q) (hyQ : y ∈ Q)
    (hg : g ∈ J) (hxy : g⁻¹ * x * g = y) :
    ∃ n ∈ J ⊓ Subgroup.normalizer (Q : Set G), n⁻¹ * x * n = y := by
  set M : Subgroup G := J ⊓ Subgroup.centralizer {x} with hM
  have hMJ : M ≤ J := inf_le_left
  have hQM : Q ≤ M := fun q hq =>
    ⟨hQ.1 hq, Subgroup.mem_centralizer_singleton_iff.mpr (hQab q hq x hxQ)⟩
  have hQM' : IsSylowTwoOf Q M := isSylowTwoOf_mono hQ hQM hMJ
  let S : Subgroup G := Q.map (MulAut.conj g).toMonoidHom
  have hS2 : IsPGroup 2 S := hQ.2.1.map _
  have hxg : x = g * y * g⁻¹ := by rw [← hxy]; group
  have hSM : S ≤ M := by
    rintro _ ⟨q, hq, rfl⟩
    have hc : g * q * g⁻¹ * x = x * (g * q * g⁻¹) :=
      calc g * q * g⁻¹ * x = g * q * g⁻¹ * (g * y * g⁻¹) := by rw [← hxg]
        _ = g * (q * y) * g⁻¹ := by group
        _ = g * (y * q) * g⁻¹ := by rw [hQab q hq y hyQ]
        _ = x * (g * q * g⁻¹) := by rw [hxg]; group
    exact ⟨J.mul_mem (J.mul_mem hg (hQ.1 hq)) (J.inv_mem hg),
      Subgroup.mem_centralizer_singleton_iff.mpr hc⟩
  obtain ⟨m, hmM, hm⟩ :=
    EscapingLocal.exists_conj_mem_of_isPGroup hQM hQM'.2.1 hQM'.2.2 hSM hS2
  have hmx : m * x = x * m := Subgroup.mem_centralizer_singleton_iff.mp hmM.2
  refine ⟨m * g, ⟨J.mul_mem (hMJ hmM) hg, ?_⟩, ?_⟩
  · refine mem_normalizer_of_conj_mem fun q hq => ?_
    have := hm (g * q * g⁻¹) ⟨q, hq, rfl⟩
    simpa [mul_assoc] using this
  · calc (m * g)⁻¹ * x * (m * g) = g⁻¹ * (m⁻¹ * x * m) * g := by group
      _ = g⁻¹ * x * g := by
        congr 2
        calc m⁻¹ * x * m = m⁻¹ * (x * m) := by group
          _ = m⁻¹ * (m * x) := by rw [hmx]
          _ = x := by group
      _ = y := hxy

omit [Finite G] in
theorem ncard_conj_class_odd {J Q : Subgroup G} (hQ : IsSylowTwoOf Q J)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) {t : G} (htQ : t ∈ Q) :
    Odd {y : G | ∃ n ∈ J ⊓ Subgroup.normalizer (Q : Set G), n⁻¹ * t * n = y}.ncard := by
  classical
  set N : Subgroup G := J ⊓ Subgroup.normalizer (Q : Set G) with hN
  let _ : MulAction N G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp N.subtype)
  have hsmul : ∀ (n : N) (x : G), n • x = (n : G) * x * (n : G)⁻¹ := fun n x => rfl
  have hset : {y : G | ∃ n ∈ N, n⁻¹ * t * n = y} = MulAction.orbit N t := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n⁻¹, N.inv_mem hn⟩, by simp [hsmul]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨((n⁻¹ : N) : G), (n⁻¹).2, by simp [hsmul]⟩
  rw [hset, ← MulAction.index_stabilizer]
  have hQN : Q ≤ N := fun q hq => ⟨hQ.1 hq, Subgroup.le_normalizer hq⟩
  have hle : Q.subgroupOf N ≤ MulAction.stabilizer N t := by
    intro q hq
    rw [MulAction.mem_stabilizer_iff, hsmul]
    have hq' : (q : G) ∈ Q := hq
    calc (q : G) * t * (q : G)⁻¹ = t * (q : G) * (q : G)⁻¹ := by rw [hQab _ hq' t htQ]
      _ = t := by group
  have h1 : (MulAction.stabilizer N t).index ∣ (Q.subgroupOf N).index :=
    Subgroup.index_dvd_of_le hle
  have h2 : (Q.subgroupOf N).index ∣ (Q.subgroupOf J).index := by
    have := Subgroup.relIndex_mul_relIndex Q N J hQN inf_le_left
    exact Dvd.intro _ this
  have hodd : ¬ 2 ∣ (MulAction.stabilizer N t).index := fun h => hQ.2.2 (h.trans (h1.trans h2))
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)

theorem exists_isolated_outer {J L Q : Subgroup G} [L.Normal] (hQ : IsSylowTwoOf Q J)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hΩ : {t : G | t ∈ Q ∧ t ∉ L}.ncard = 4) :
    ∃ t ∈ Q, t ∉ L ∧ ∀ g ∈ J, g⁻¹ * t * g ∈ Q → g⁻¹ * t * g = t := by
  classical
  set N : Subgroup G := J ⊓ Subgroup.normalizer (Q : Set G) with hN
  set Ω : Set G := {t : G | t ∈ Q ∧ t ∉ L} with hΩdef
  let C : G → Set G := fun t => {y : G | ∃ n ∈ N, n⁻¹ * t * n = y}
  have hCΩ : ∀ t ∈ Ω, C t ⊆ Ω := by
    rintro t ⟨htQ, htL⟩ _ ⟨n, hn, rfl⟩
    refine ⟨?_, fun h => htL ?_⟩
    · have hn' : n⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
        (Subgroup.normalizer (Q : Set G)).inv_mem hn.2
      have := (Subgroup.mem_normalizer_iff.mp hn' t).mp htQ
      simpa using this
    · have := Subgroup.Normal.conj_mem ‹L.Normal› _ h n
      simpa [mul_assoc] using this
  have hCt : ∀ t, t ∈ C t := fun t => ⟨1, N.one_mem, by simp⟩
  by_contra hcon
  push Not at hcon
  have hbig : ∀ t ∈ Ω, 2 ≤ (C t).ncard := by
    intro t ht
    obtain ⟨g, hg, hgQ, hne⟩ := hcon t ht.1 ht.2
    obtain ⟨n, hn, hn'⟩ := burnside_abelian hQ hQab ht.1 hgQ hg rfl
    have hsub : ({t, g⁻¹ * t * g} : Set G) ⊆ C t := by
      intro y hy
      rcases hy with rfl | rfl
      · exact hCt _
      · exact ⟨n, hn, hn'⟩
    have h2 : ({t, g⁻¹ * t * g} : Set G).ncard = 2 := Set.ncard_pair (Ne.symm hne)
    calc 2 = ({t, g⁻¹ * t * g} : Set G).ncard := h2.symm
      _ ≤ (C t).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hodd : ∀ t ∈ Ω, Odd (C t).ncard := fun t ht => ncard_conj_class_odd hQ hQab ht.1
  have hle : ∀ t ∈ Ω, (C t).ncard ≤ 4 := fun t ht =>
    hΩ ▸ Set.ncard_le_ncard (hCΩ t ht) (Set.toFinite _)
  have hne : Ω.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨t₁, ht₁⟩ := hne
  have h3 : (C t₁).ncard = 3 := by
    have := hbig t₁ ht₁
    have := hodd t₁ ht₁
    have := hle t₁ ht₁
    obtain ⟨k, hk⟩ := ‹Odd (C t₁).ncard›
    omega
  have hdiff : (Ω \ C t₁).ncard = 1 := by
    rw [Set.ncard_sdiff (hCΩ t₁ ht₁) (Set.toFinite _), hΩ, h3]
  obtain ⟨t₂, ht₂⟩ := Set.nonempty_of_ncard_ne_zero (s := Ω \ C t₁) (by omega)
  have hCt₂ : C t₂ ⊆ Ω \ C t₁ := by
    intro y hy
    refine ⟨hCΩ t₂ ht₂.1 hy, fun hy1 => ht₂.2 ?_⟩
    obtain ⟨n₂, hn₂, rfl⟩ := hy
    obtain ⟨n₁, hn₁, hn₁y⟩ := hy1
    refine ⟨n₁ * n₂⁻¹, N.mul_mem hn₁ (N.inv_mem hn₂), ?_⟩
    have : t₂ = n₂ * (n₂⁻¹ * t₂ * n₂) * n₂⁻¹ := by group
    rw [this, ← hn₁y]
    group
  have h4 := Set.ncard_le_ncard hCt₂ (Set.toFinite _)
  have h5 := hbig t₂ ht₂.1
  omega

end Burnside

section Core

omit [Finite G] in
@[expose] def NoStrongAb (L : Subgroup G) : Prop :=
  ∀ Q B : Subgroup G, IsSylowTwoOf Q L → B ≤ Q → IsMulCommutative B →
    (∀ a ∈ B, ∀ g ∈ L, g⁻¹ * a * g ∈ Q → g⁻¹ * a * g ∈ B) → B = ⊥

omit [Finite G] in
theorem mem_sup_zpowers_of_sq {L : Subgroup G} [L.Normal] {a : G} (ha : a * a = 1) {x : G}
    (hx : x ∈ L ⊔ Subgroup.zpowers a) : x ∈ L ∨ ∃ l ∈ L, x = l * a := by
  obtain ⟨l, hl, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hsq : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha]
  have hk : a ^ k = a ^ (k % 2) := by
    calc a ^ k = a ^ (k % 2 + 2 * (k / 2)) := by rw [Int.emod_add_mul_ediv]
      _ = a ^ (k % 2) := by rw [zpow_add, zpow_mul, hsq, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, zpow_zero, mul_one]; exact hl
  · right
    refine ⟨l, hl, ?_⟩
    rw [hk, h, zpow_one]

omit [Finite G] in
theorem isMulCommutative_of_le {A B : Subgroup G} (hA : IsMulCommutative A) (hBA : B ≤ A) :
    IsMulCommutative B :=
  ⟨⟨fun x y => Subtype.ext (by
    have h := hA.is_comm.comm ⟨x.1, hBA x.2⟩ ⟨y.1, hBA y.2⟩
    have h' : (x.1 * y.1 : G) = y.1 * x.1 := congrArg Subtype.val h
    exact h')⟩⟩

omit [Finite G] in
theorem conj_mem_sup_zpowers {L : Subgroup G} [L.Normal] {A : Subgroup G}
    (hA : IsMulCommutative A) {a : G} (ha : a ∈ A) (ha2 : a * a = 1) :
    ∀ b ∈ A, ∀ j ∈ L ⊔ Subgroup.zpowers a, b * j * b⁻¹ ∈ L ⊔ Subgroup.zpowers a := by
  intro b hb j hj
  have hLJ : L ≤ L ⊔ Subgroup.zpowers a := le_sup_left
  have haJ : a ∈ L ⊔ Subgroup.zpowers a := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  rcases mem_sup_zpowers_of_sq ha2 hj with h | ⟨l, hl, rfl⟩
  · exact hLJ (Subgroup.Normal.conj_mem ‹L.Normal› j h b)
  · have hba : b * a = a * b := congrArg Subtype.val (hA.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
    have h1 : b * a * b⁻¹ = a := by rw [hba]; group
    have : b * (l * a) * b⁻¹ = (b * l * b⁻¹) * (b * a * b⁻¹) := by group
    rw [this, h1]
    exact (L ⊔ Subgroup.zpowers a).mul_mem (hLJ (Subgroup.Normal.conj_mem ‹L.Normal› l hl b)) haJ

theorem centralizes_of_inf_bot {L A Q : Subgroup G} [L.Normal] (hL : IsSimpleGroup L)
    (hev : 2 ∣ Nat.card L) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) (ha2 : a * a = 1)
    (hbot : A ⊓ L = ⊥) (hQ : IsSylowTwoOf Q (L ⊔ Subgroup.zpowers a))
    (hclJ : ∀ b ∈ A ⊓ (L ⊔ Subgroup.zpowers a), ∀ g ∈ L ⊔ Subgroup.zpowers a,
      g⁻¹ * b * g ∈ Q → g⁻¹ * b * g ∈ A ⊓ (L ⊔ Subgroup.zpowers a)) :
    a ∈ Subgroup.centralizer (L : Set G) := by
  have hLJ : L ≤ L ⊔ Subgroup.zpowers a := le_sup_left
  have haJ : a ∈ L ⊔ Subgroup.zpowers a := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hB : ∀ b ∈ A ⊓ (L ⊔ Subgroup.zpowers a), b = 1 ∨ b = a := by
    intro b hb
    rcases mem_sup_zpowers_of_sq ha2 hb.2 with h | ⟨l, hl, rfl⟩
    · left
      have : b ∈ A ⊓ L := ⟨hb.1, h⟩
      rw [hbot, Subgroup.mem_bot] at this; exact this
    · right
      have hlA : l ∈ A := by
        have := A.mul_mem hb.1 (A.inv_mem ha)
        simpa using this
      have : l ∈ A ⊓ L := ⟨hlA, hl⟩
      rw [hbot, Subgroup.mem_bot] at this
      rw [this, one_mul]
  have hwc : ∀ g ∈ L ⊔ Subgroup.zpowers a, g⁻¹ * a * g ∈ Q → g⁻¹ * a * g = a := by
    intro g hg hgQ
    have h1 := hclJ a ⟨ha, haJ⟩ g hg hgQ
    rcases hB _ h1 with h | h
    · exfalso; apply ha1
      have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      rw [this, h]; group
    · exact h
  exact centralizes_of_isolated hLJ hL hev haJ ha1 ha2 (isolated_of_closed hQ haJ ha2 hwc)

theorem core_nasc {L : Subgroup G} [L.Normal] (hL : IsSimpleGroup L) (hev : 2 ∣ Nat.card L)
    (hN : NoStrongAb L) {R A : Subgroup G} (hR : IsSylowTwoOf R ⊤) (hAR : A ≤ R)
    (hA : IsElemAbelian 2 A) (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ R → g⁻¹ * a * g ∈ A) :
    A ≤ Subgroup.centralizer (L : Set G) := by
  intro a ha
  by_cases ha1 : a = 1
  · rw [ha1]; exact Subgroup.one_mem _
  have ha2 : a * a = 1 := by simpa [sq] using hA.2 a ha
  have hLJ : L ≤ L ⊔ Subgroup.zpowers a := le_sup_left
  obtain ⟨Q, hQ, hAQ, hclJ⟩ :=
    exists_sylow_closed hR hAR hcl (conj_mem_sup_zpowers (L := L) hA.1 ha ha2)
  have hLn : (L.subgroupOf (L ⊔ Subgroup.zpowers a)).Normal := inferInstance
  have hQL : IsSylowTwoOf (Q ⊓ L) L :=
    isSylowTwoOf_inf_of_subnormal hQ hLJ hLn.isSubnormal
  have hbot : A ⊓ L = ⊥ := by
    refine hN (Q ⊓ L) (A ⊓ L) hQL (fun x hx => ⟨hAQ ⟨hx.1, hLJ hx.2⟩, hx.2⟩)
      (isMulCommutative_of_le hA.1 inf_le_left) ?_
    intro x hx g hg hgQ
    have hx' : x ∈ A ⊓ (L ⊔ Subgroup.zpowers a) := ⟨hx.1, hLJ hx.2⟩
    have := hclJ x hx' g (hLJ hg) hgQ.1
    exact ⟨this.1, L.mul_mem (L.mul_mem (L.inv_mem hg) hx.2) hg⟩
  exact centralizes_of_inf_bot hL hev ha ha1 ha2 hbot hQ hclJ

theorem core_four {L : Subgroup G} [L.Normal] (hL : IsSimpleGroup L)
    (hnonab : ∃ x y : L, x * y ≠ y * x) (hev : 2 ∣ Nat.card L)
    (h4 : ∀ Q : Subgroup G, IsSylowTwoOf Q L → Nat.card Q = 4)
    {R A : Subgroup G} (hR : IsSylowTwoOf R ⊤) (hAR : A ≤ R) (hA : IsElemAbelian 2 A)
    (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ R → g⁻¹ * a * g ∈ A) :
    ∀ a ∈ A, ∃ l ∈ L, a * l ∈ Subgroup.centralizer (L : Set G) := by
  intro a ha
  by_cases haL : a ∈ L
  · exact ⟨a⁻¹, L.inv_mem haL, by rw [mul_inv_cancel]; exact Subgroup.one_mem _⟩
  have ha1 : a ≠ 1 := fun h => haL (h ▸ L.one_mem)
  have ha2 : a * a = 1 := by simpa [sq] using hA.2 a ha
  have hLJ : L ≤ L ⊔ Subgroup.zpowers a := le_sup_left
  have haJ : a ∈ L ⊔ Subgroup.zpowers a := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  obtain ⟨Q, hQ, hAQ, hclJ⟩ :=
    exists_sylow_closed hR hAR hcl (conj_mem_sup_zpowers (L := L) hA.1 ha ha2)
  have hLn : (L.subgroupOf (L ⊔ Subgroup.zpowers a)).Normal := inferInstance
  have hQL : IsSylowTwoOf (Q ⊓ L) L :=
    isSylowTwoOf_inf_of_subnormal hQ hLJ hLn.isSubnormal
  have hcard : Nat.card (Q ⊓ L : Subgroup G) = 4 := h4 _ hQL
  have hB₀le : A ⊓ L ≤ Q ⊓ L := fun x hx => ⟨hAQ ⟨hx.1, hLJ hx.2⟩, hx.2⟩
  have hdvd : Nat.card (A ⊓ L : Subgroup G) ∣ 4 := hcard ▸ Subgroup.card_dvd_of_le hB₀le
  have hcases : Nat.card (A ⊓ L : Subgroup G) = 1 ∨ Nat.card (A ⊓ L : Subgroup G) = 2 ∨
      Nat.card (A ⊓ L : Subgroup G) = 4 := by
    have hdvd' : Nat.card (A ⊓ L : Subgroup G) ∣ 2 ^ 2 := by simpa using hdvd
    obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    interval_cases m <;> simp_all
  rcases hcases with h1 | h2 | h4'
  · have hbot : A ⊓ L = ⊥ := Subgroup.card_eq_one.mp h1
    exact ⟨1, L.one_mem, by
      rw [mul_one]; exact centralizes_of_inf_bot hL hev ha ha1 ha2 hbot hQ hclJ⟩
  · exfalso
    have hex : ∃ c ∈ A ⊓ L, c ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : A ⊓ L = ⊥ := Subgroup.eq_bot_iff_forall _ |>.mpr hcon
      rw [this, Subgroup.card_bot] at h2
      omega
    obtain ⟨c, hc, hc1⟩ := hex
    have huniq : ∀ x ∈ A ⊓ L, x = 1 ∨ x = c := by
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · right
        obtain ⟨y, _, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(A ⊓ L))).mp h2
        have h1' : (⟨x, hx⟩ : ↥(A ⊓ L)) = y := hy _ (fun h => hx1 (congrArg Subtype.val h))
        have h2' : (⟨c, hc⟩ : ↥(A ⊓ L)) = y := hy _ (fun h => hc1 (congrArg Subtype.val h))
        exact congrArg Subtype.val (h1'.trans h2'.symm)
    have hc2 : c * c = 1 := by simpa [sq] using hA.2 c hc.1
    have hcJ : c ∈ L ⊔ Subgroup.zpowers a := hLJ hc.2
    have hwc : ∀ g ∈ L ⊔ Subgroup.zpowers a, g⁻¹ * c * g ∈ Q → g⁻¹ * c * g = c := by
      intro g hg hgQ
      have h1 := hclJ c ⟨hc.1, hcJ⟩ g hg hgQ
      have h2 : g⁻¹ * c * g ∈ L := by
        have := Subgroup.Normal.conj_mem ‹L.Normal› c hc.2 g⁻¹
        simpa using this
      rcases huniq _ ⟨h1.1, h2⟩ with h | h
      · exfalso; apply hc1
        have : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
        rw [this, h]; group
      · exact h
    have hcent :=
      centralizes_of_isolated hLJ hL hev hcJ hc1 hc2 (isolated_of_closed hQ hcJ hc2 hwc)
    have hcenter : (⟨c, hc.2⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext (by
        have := Subgroup.mem_centralizer_iff.mp hcent x.1 x.2
        exact this)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · rw [h, Subgroup.mem_bot] at hcenter
      exact hc1 (congrArg Subtype.val hcenter)
    · obtain ⟨x, y, hxy⟩ := hnonab
      apply hxy
      have hx : x ∈ Subgroup.center L := h ▸ Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.mp hx y).symm
  · have hQ_eq : A ⊓ L = Q ⊓ L :=
      Subgroup.eq_of_le_of_card_ge hB₀le (by rw [hcard, h4'])
    have haQ : a ∈ Q := hAQ ⟨ha, haJ⟩
    have hQA : Q ≤ A := by
      intro q hq
      rcases mem_sup_zpowers_of_sq ha2 (hQ.1 hq) with h | ⟨l, hl, rfl⟩
      · have : q ∈ Q ⊓ L := ⟨hq, h⟩
        rw [← hQ_eq] at this; exact this.1
      · have hlQ : l ∈ Q := by
          have := Q.mul_mem hq (Q.inv_mem haQ)
          simpa using this
        have : l ∈ Q ⊓ L := ⟨hlQ, hl⟩
        rw [← hQ_eq] at this
        exact A.mul_mem this.1 ha
    have hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hQA hx⟩ ⟨y, hQA hy⟩)
    have hΩ : {t : G | t ∈ Q ∧ t ∉ L}.ncard = 4 := by
      have : {t : G | t ∈ Q ∧ t ∉ L} =
          (fun x => x * a) '' ((Q ⊓ L : Subgroup G) : Set G) := by
        ext t
        constructor
        · rintro ⟨htQ, htL⟩
          rcases mem_sup_zpowers_of_sq ha2 (hQ.1 htQ) with h | ⟨l, hl, rfl⟩
          · exact absurd h htL
          · have hlQ : l ∈ Q := by
              have := Q.mul_mem htQ (Q.inv_mem haQ)
              simpa using this
            exact ⟨l, ⟨hlQ, hl⟩, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨Q.mul_mem hx.1 haQ, fun h => haL (by
            have := L.mul_mem (L.inv_mem hx.2) h
            simpa using this)⟩
      rw [this, Set.ncard_image_of_injective _ (mul_left_injective a)]
      rw [← Nat.card_coe_set_eq]
      exact hcard
    obtain ⟨t, htQ, htL, hwc⟩ :=
      exists_isolated_outer (J := L ⊔ Subgroup.zpowers a) (L := L) hQ hQab hΩ
    have htJ : t ∈ L ⊔ Subgroup.zpowers a := hQ.1 htQ
    have ht2 : t * t = 1 := by simpa [sq] using hA.2 t (hQA htQ)
    have ht1 : t ≠ 1 := fun h => htL (h ▸ L.one_mem)
    have hcent :=
      centralizes_of_isolated hLJ hL hev htJ ht1 ht2 (isolated_of_closed hQ htJ ht2 hwc)
    rcases mem_sup_zpowers_of_sq ha2 htJ with h | ⟨l₁, hl₁, rfl⟩
    · exact absurd h htL
    · refine ⟨a⁻¹ * l₁ * a, ?_, ?_⟩
      · have := Subgroup.Normal.conj_mem ‹L.Normal› l₁ hl₁ a⁻¹
        simpa using this
      · have : a * (a⁻¹ * l₁ * a) = l₁ * a := by group
        rw [this]; exact hcent

end Core

end CFSG.QuasithinUnique.K1
