module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

structure A10GammaStructAt (K : Type) [Group K] [Finite K] (S Λ₁ Λ₂ : Subgroup K) : Prop where
  le_gamma₁ : Λ₁ ≤ A10Gamma K S
  le_gamma₂ : Λ₂ ≤ A10Gamma K S
  inf_bot : Λ₁ ⊓ Λ₂ = ⊥
  comm : ∀ a ∈ Λ₁, ∀ b ∈ Λ₂, a * b = b * a
  iso₁ : Nonempty (↥Λ₁ ≃* alternatingGroup (Fin 5))
  iso₂ : Nonempty (↥Λ₂ ≃* alternatingGroup (Fin 5))
  five : ∀ g ∈ A10Gamma K S, (∃ k : ℕ, g ^ 5 ^ k = 1) → g ∈ Λ₁ ⊔ Λ₂
  S_card₁ : Nat.card ↥(S ⊓ Λ₁) = 5
  S_card₂ : Nat.card ↥(S ⊓ Λ₂) = 5
  S_sup : (S ⊓ Λ₁) ⊔ (S ⊓ Λ₂) = S
  cent₃₀₀ : ∀ s ∈ S, s ≠ 1 → (s ∈ Λ₁ ∨ s ∈ Λ₂) → Nat.card ↥(Subgroup.centralizer ({s} : Set K)) = 300
  cent₂₅ : ∀ s ∈ S, s ∉ Λ₁ → s ∉ Λ₂ → Nat.card ↥(Subgroup.centralizer ({s} : Set K)) = 25
  swap : ∃ n ∈ Subgroup.normalizer (S : Set K), Λ₁.map (MulAut.conj n).toMonoidHom = Λ₂

@[expose] def A10Irred (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow 5 K, ∀ A : Subgroup K, A ≤ (S : Subgroup K) →
    (∀ n ∈ Subgroup.normalizer ((S : Subgroup K) : Set K), ∀ a ∈ A, n * a * n⁻¹ ∈ A) →
    A = ⊥ ∨ A = (S : Subgroup K)

structure A10L43Facts : Prop where
  gammaStruct : ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → ∀ S : Sylow 5 K,
    ∃ Λ₁ Λ₂ : Subgroup K, A10GammaStructAt K (S : Subgroup K) Λ₁ Λ₂
  irred : ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → A10Irred K

theorem a10t1_gf_fiveRes_le {G : Type} [Group G] (H : Subgroup G) : fiveRes H ≤ H := by
  unfold fiveRes
  exact (Subgroup.closure_le H).mpr (fun _ hg => hg.1)

theorem a10t1_gf_fiveRes_mono {G : Type} [Group G] {H H' : Subgroup G} (h : H ≤ H') :
    fiveRes H ≤ fiveRes H' := by
  unfold fiveRes
  exact Subgroup.closure_mono (fun _ hg => ⟨h hg.1, hg.2⟩)

theorem a10t1_gf_fiveRes_conj {G : Type} [Group G] (H : Subgroup G) {g : G} (hg : g ∈ H) {x : G}
    (hx : x ∈ fiveRes H) : g * x * g⁻¹ ∈ fiveRes H := by
  unfold fiveRes at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    refine Subgroup.subset_closure ⟨H.mul_mem (H.mul_mem hg hy.1) (H.inv_mem hg), ?_⟩
    obtain ⟨k, hk⟩ := hy.2
    exact ⟨k, by rw [conj_pow, hk]; simp⟩
  | one => simp
  | mul y z _ _ hy hz =>
    have e : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
    have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hy

theorem a10t1_gf_card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  norm_num [Nat.factorial]

theorem a10t1_gf_fiveRes_eq_of_iso {K : Type} [Group K] [Finite K] {Λ : Subgroup K}
    (e : ↥Λ ≃* alternatingGroup (Fin 5)) : fiveRes Λ = Λ := by
  refine le_antisymm (a10t1_gf_fiveRes_le Λ) ?_
  haveI hsimple : IsSimpleGroup ↥Λ := e.isSimpleGroup
  haveI hN : ((fiveRes Λ).subgroupOf Λ).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact a10t1_gf_fiveRes_conj Λ g.2 hx⟩
  have hcard : Nat.card ↥Λ = 60 := by
    rw [Nat.card_congr e.toEquiv]; exact a10t1_gf_card_alt5
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥Λ) 5 (by rw [hcard]; norm_num)
  rcases hsimple.eq_bot_or_eq_top_of_normal ((fiveRes Λ).subgroupOf Λ) with h | h
  · exfalso
    have hgN : g ∈ (fiveRes Λ).subgroupOf Λ := by
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.subset_closure ⟨g.2, 1, ?_⟩
      have h5 : g ^ 5 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
      have := congrArg (fun z : ↥Λ => (z : K)) h5
      simpa using this
    rw [h, Subgroup.mem_bot] at hgN
    rw [hgN, orderOf_one] at hg
    omega
  · intro y hy
    have : (⟨y, hy⟩ : ↥Λ) ∈ (fiveRes Λ).subgroupOf Λ := by rw [h]; trivial
    exact Subgroup.mem_subgroupOf.mp this

theorem a10g_five_gen {K : Type} [Group K] [Finite K] {S Λ₁ Λ₂ : Subgroup K}
    (h : A10GammaStructAt K S Λ₁ Λ₂) :
    fiveRes Λ₁ = Λ₁ ∧ fiveRes Λ₂ = Λ₂ := by
  obtain ⟨e₁⟩ := h.iso₁
  obtain ⟨e₂⟩ := h.iso₂
  exact ⟨a10t1_gf_fiveRes_eq_of_iso e₁, a10t1_gf_fiveRes_eq_of_iso e₂⟩

theorem a10t1_gf_fiveRes_map {K : Type} [Group K] (φ : MulAut K) (H : Subgroup K) :
    (fiveRes H).map φ.toMonoidHom = fiveRes (H.map φ.toMonoidHom) := by
  unfold fiveRes
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨g, ⟨hgH, k, hk⟩, rfl⟩
    refine ⟨⟨g, hgH, rfl⟩, k, ?_⟩
    show (φ g) ^ 5 ^ k = 1
    rw [← map_pow, hk, map_one]
  · rintro ⟨⟨g, hgH, rfl⟩, k, hk⟩
    refine ⟨g, ⟨hgH, k, ?_⟩, rfl⟩
    have h1 : φ (g ^ 5 ^ k) = 1 := by rw [map_pow]; exact hk
    exact φ.injective (by rw [h1, map_one])

theorem a10t1_gf_gamma_fiveRes {K : Type} [Group K] [Finite K] {S Λ₁ Λ₂ : Subgroup K}
    (h : A10GammaStructAt K S Λ₁ Λ₂) : fiveRes (A10Gamma K S) = Λ₁ ⊔ Λ₂ := by
  obtain ⟨h1, h2⟩ := a10g_five_gen h
  apply le_antisymm
  · unfold fiveRes
    exact (Subgroup.closure_le _).mpr (fun g hg => h.five g hg.1 hg.2)
  · exact sup_le (h1.symm.le.trans (a10t1_gf_fiveRes_mono h.le_gamma₁))
      (h2.symm.le.trans (a10t1_gf_fiveRes_mono h.le_gamma₂))

theorem a10t1_gf_sup_decomp {K : Type} [Group K] {A B : Subgroup K}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {t : K} (ht : t ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, t = a * b := by
  rw [Subgroup.sup_eq_closure] at ht
  induction ht using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hy, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    obtain ⟨a', ha', b', hb', rfl⟩ := hz
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    have e : b * a' = a' * b := (hcomm a' ha' b hb).symm
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [e]
      _ = a * a' * (b * b') := by group
  | inv y _ hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    rw [mul_inv_rev]
    exact (hcomm _ (A.inv_mem ha) _ (B.inv_mem hb)).symm

theorem a10t1_gf_sup_norm_left {K : Type} [Group K] {A B : Subgroup K}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {n : K} (hn : n ∈ A ⊔ B) {x : K} (hx : x ∈ A) :
    n * x * n⁻¹ ∈ A := by
  obtain ⟨a, ha, b, hb, rfl⟩ := a10t1_gf_sup_decomp hcomm hn
  have h1 : b * x = x * b := (hcomm x hx b hb).symm
  have e : a * b * x * (a * b)⁻¹ = a * x * a⁻¹ := by
    calc a * b * x * (a * b)⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ := by group
      _ = a * (x * b) * b⁻¹ * a⁻¹ := by rw [h1]
      _ = a * x * a⁻¹ := by group
  rw [e]
  exact A.mul_mem (A.mul_mem ha hx) (A.inv_mem ha)

theorem a10t1_gf_sup_norm_right {K : Type} [Group K] {A B : Subgroup K}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {n : K} (hn : n ∈ A ⊔ B) {x : K} (hx : x ∈ B) :
    n * x * n⁻¹ ∈ B :=
  a10t1_gf_sup_norm_left (A := B) (B := A) (fun b hb a ha => (hcomm a ha b hb).symm)
    (by rwa [sup_comm]) hx

theorem a10t1_gf_inf_normal {K : Type} [Group K] {A T : Subgroup K} (hA : IsSimpleGroup ↥A)
    (hn : ∀ a ∈ A, ∀ t ∈ T, a * t * a⁻¹ ∈ T) : T ⊓ A = ⊥ ∨ A ≤ T := by
  haveI : ((T ⊓ A).subgroupOf A).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxT, hxA⟩ := hx
    exact ⟨hn g.1 g.2 x hxT, A.mul_mem (A.mul_mem g.2 hxA) (A.inv_mem g.2)⟩⟩
  rcases hA.eq_bot_or_eq_top_of_normal ((T ⊓ A).subgroupOf A) with h | h
  · left
    refine Subgroup.eq_bot_iff_forall _ |>.mpr (fun x hx => ?_)
    have h1 : (⟨x, hx.2⟩ : ↥A) ∈ (T ⊓ A).subgroupOf A := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at h1
    simpa using congrArg Subtype.val h1
  · right
    intro a ha
    have h1 : (⟨a, ha⟩ : ↥A) ∈ (T ⊓ A).subgroupOf A := by rw [h]; trivial
    exact (Subgroup.mem_subgroupOf.mp h1).1

theorem a10t1_gf_centreless {G : Type} [Group G] {n : ℕ} (hn : 4 ≤ n)
    (e : G ≃* alternatingGroup (Fin n)) (z : G) (hz : ∀ g : G, z * g = g * z) : z = 1 := by
  have hz' : e z ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨u, rfl⟩ := e.surjective y
    have h1 : e (u * z) = e (z * u) := by rw [hz u]
    rwa [map_mul, map_mul] at h1
  rw [alternatingGroup.center_eq_bot (by simpa using hn), Subgroup.mem_bot] at hz'
  exact e.injective (by rw [hz', map_one])

theorem a10t1_gf_normal_factor {K : Type} [Group K] {A B T : Subgroup K}
    (hA : IsSimpleGroup ↥A) (hB : IsSimpleGroup ↥B) (hT : IsSimpleGroup ↥T)
    (hTc : ∀ t₁ ∈ T, (∀ t₂ ∈ T, t₁ * t₂ = t₂ * t₁) → t₁ = 1)
    (hAB : A ⊓ B = ⊥) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hTN : T ≤ A ⊔ B) (hTnorm : ∀ n ∈ A ⊔ B, ∀ t ∈ T, n * t * n⁻¹ ∈ T) :
    T = A ∨ T = B := by
  have hAne : A ≠ ⊥ := (Subgroup.isSimpleGroup_iff.mp hA).1
  have hBne : B ≠ ⊥ := (Subgroup.isSimpleGroup_iff.mp hB).1
  have hTne : T ≠ ⊥ := (Subgroup.isSimpleGroup_iff.mp hT).1
  have hAn : ∀ n ∈ A ⊔ B, ∀ x ∈ A, n * x * n⁻¹ ∈ A := fun n hn x hx =>
    a10t1_gf_sup_norm_left hcomm hn hx
  have hBn : ∀ n ∈ A ⊔ B, ∀ x ∈ B, n * x * n⁻¹ ∈ B := fun n hn x hx =>
    a10t1_gf_sup_norm_right hcomm hn hx
  rcases a10t1_gf_inf_normal hA (fun a ha t ht => hTnorm a (Subgroup.mem_sup_left ha) t ht) with
      hTA | hAT <;>
  rcases a10t1_gf_inf_normal hB (fun b hb t ht => hTnorm b (Subgroup.mem_sup_right hb) t ht) with
      hTB | hBT
  ·
    exfalso
    apply hTne
    rw [Subgroup.eq_bot_iff_forall]
    intro t ht
    apply hTc t ht
    intro t₂ ht₂
    have hcA : ∀ a ∈ A, t * a = a * t := by
      intro a ha
      have h1 : t * a * t⁻¹ * a⁻¹ ∈ T ⊓ A := by
        refine ⟨?_, ?_⟩
        · have h2 := hTnorm a (Subgroup.mem_sup_left ha) t⁻¹ (T.inv_mem ht)
          have e : t * a * t⁻¹ * a⁻¹ = t * (a * t⁻¹ * a⁻¹) := by group
          rw [e]
          exact T.mul_mem ht h2
        · exact A.mul_mem (hAn t (hTN ht) a ha) (A.inv_mem ha)
      rw [hTA, Subgroup.mem_bot] at h1
      calc t * a = t * a * t⁻¹ * a⁻¹ * (a * t) := by group
        _ = a * t := by rw [h1, one_mul]
    have hcB : ∀ b ∈ B, t * b = b * t := by
      intro b hb
      have h1 : t * b * t⁻¹ * b⁻¹ ∈ T ⊓ B := by
        refine ⟨?_, ?_⟩
        · have h2 := hTnorm b (Subgroup.mem_sup_right hb) t⁻¹ (T.inv_mem ht)
          have e : t * b * t⁻¹ * b⁻¹ = t * (b * t⁻¹ * b⁻¹) := by group
          rw [e]
          exact T.mul_mem ht h2
        · exact B.mul_mem (hBn t (hTN ht) b hb) (B.inv_mem hb)
      rw [hTB, Subgroup.mem_bot] at h1
      calc t * b = t * b * t⁻¹ * b⁻¹ * (b * t) := by group
        _ = b * t := by rw [h1, one_mul]
    obtain ⟨a, ha, b, hb, rfl⟩ := a10t1_gf_sup_decomp hcomm (hTN ht₂)
    calc t * (a * b) = (t * a) * b := by group
      _ = (a * t) * b := by rw [hcA a ha]
      _ = a * (t * b) := by group
      _ = a * (b * t) := by rw [hcB b hb]
      _ = a * b * t := by group
  ·
    right
    apply le_antisymm
    · intro t ht
      obtain ⟨a, ha, b, hb, rfl⟩ := a10t1_gf_sup_decomp hcomm (hTN ht)
      have haT : a ∈ T := by
        have e : a = (a * b) * b⁻¹ := by group
        rw [e]
        exact T.mul_mem ht (T.inv_mem (hBT hb))
      have h1 : a ∈ T ⊓ A := ⟨haT, ha⟩
      rw [hTA, Subgroup.mem_bot] at h1
      rw [h1, one_mul]
      exact hb
    · exact hBT
  ·
    left
    apply le_antisymm
    · intro t ht
      obtain ⟨a, ha, b, hb, rfl⟩ := a10t1_gf_sup_decomp hcomm (hTN ht)
      have hbT : b ∈ T := by
        have e : b = a⁻¹ * (a * b) := by group
        rw [e]
        exact T.mul_mem (T.inv_mem (hAT ha)) ht
      have h1 : b ∈ T ⊓ B := ⟨hbT, hb⟩
      rw [hTB, Subgroup.mem_bot] at h1
      rw [h1, mul_one]
      exact ha
    · exact hAT
  ·
    exfalso
    have hTA' : T ≤ A := by
      rcases a10t1_gf_inf_normal hT (fun t ht x hx => hAn t (hTN ht) x hx) with h1 | h1
      · exact absurd (((inf_eq_left.mpr hAT).symm).trans h1) hAne
      · exact h1
    have h2 : B ≤ A ⊓ B := le_inf (hBT.trans hTA') le_rfl
    rw [hAB] at h2
    exact hBne (le_bot_iff.mp h2)

theorem a10g_aut_perm {K : Type} [Group K] [Finite K] {S Λ₁ Λ₂ : Subgroup K}
    (h : A10GammaStructAt K S Λ₁ Λ₂) (φ : MulAut K)
    (hφ : (A10Gamma K S).map φ.toMonoidHom = A10Gamma K S) :
    (Λ₁.map φ.toMonoidHom = Λ₁ ∧ Λ₂.map φ.toMonoidHom = Λ₂) ∨
      (Λ₁.map φ.toMonoidHom = Λ₂ ∧ Λ₂.map φ.toMonoidHom = Λ₁) := by
  obtain ⟨e₁⟩ := h.iso₁
  obtain ⟨e₂⟩ := h.iso₂
  have hs₁ : IsSimpleGroup ↥Λ₁ := e₁.isSimpleGroup
  have hs₂ : IsSimpleGroup ↥Λ₂ := e₂.isSimpleGroup
  have hN : (Λ₁ ⊔ Λ₂).map φ.toMonoidHom = Λ₁ ⊔ Λ₂ := by
    rw [← a10t1_gf_gamma_fiveRes h, a10t1_gf_fiveRes_map, hφ]
  have hne : Λ₁ ≠ Λ₂ := by
    intro h12
    have hbot : Λ₁ = ⊥ := by
      have h3 : Λ₁ ⊓ Λ₂ = Λ₁ := by rw [← h12]; exact inf_idem Λ₁
      rw [← h3, h.inf_bot]
    exact (Subgroup.isSimpleGroup_iff.mp hs₁).1 hbot
  have himg : ∀ (A : Subgroup K), (↥A ≃* alternatingGroup (Fin 5)) → A ≤ Λ₁ ⊔ Λ₂ →
      (∀ n ∈ Λ₁ ⊔ Λ₂, ∀ x ∈ A, n * x * n⁻¹ ∈ A) →
      (A.map φ.toMonoidHom = Λ₁ ∨ A.map φ.toMonoidHom = Λ₂) := by
    intro A e hAN hAn
    have eT : ↥(A.map φ.toMonoidHom) ≃* alternatingGroup (Fin 5) :=
      (Subgroup.equivMapOfInjective A φ.toMonoidHom φ.injective).symm.trans e
    have hsT : IsSimpleGroup ↥(A.map φ.toMonoidHom) := eT.isSimpleGroup
    refine a10t1_gf_normal_factor hs₁ hs₂ hsT ?_ h.inf_bot h.comm ?_ ?_
    · intro t₁ ht₁ hc
      have h1 := a10t1_gf_centreless (by norm_num) eT ⟨t₁, ht₁⟩
        (fun g => Subtype.ext (hc g.1 g.2))
      exact congrArg Subtype.val h1
    · rw [← hN]
      exact Subgroup.map_mono hAN
    · intro n hn t ht
      obtain ⟨x, hx, rfl⟩ := ht
      have hn' : n ∈ (Λ₁ ⊔ Λ₂).map φ.toMonoidHom := by rw [hN]; exact hn
      obtain ⟨m, hm, rfl⟩ := hn'
      exact ⟨m * x * m⁻¹, hAn m hm x hx, by simp⟩
  have c₁ := himg Λ₁ e₁ le_sup_left (fun n hn x hx => a10t1_gf_sup_norm_left h.comm hn hx)
  have c₂ := himg Λ₂ e₂ le_sup_right (fun n hn x hx => a10t1_gf_sup_norm_right h.comm hn hx)
  have hmapne : Λ₁.map φ.toMonoidHom ≠ Λ₂.map φ.toMonoidHom := fun he =>
    hne (Subgroup.map_injective φ.injective he)
  rcases c₁ with c₁ | c₁ <;> rcases c₂ with c₂ | c₂
  · exact absurd (c₁.trans c₂.symm) hmapne
  · exact Or.inl ⟨c₁, c₂⟩
  · exact Or.inr ⟨c₁, c₂⟩
  · exact absurd (c₁.trans c₂.symm) hmapne

theorem a10g_aut5 (hX : A10Facts) (hXe : A10Ext) {K : Type} [Group K] [Finite K] (hK : IsA10Type 5 K)
    {S : Sylow 5 K} {Λ₁ Λ₂ : Subgroup K} (h : A10GammaStructAt K (S : Subgroup K) Λ₁ Λ₂) (φ : MulAut K)
    (hφ : (A10Gamma K (S : Subgroup K)).map φ.toMonoidHom = A10Gamma K (S : Subgroup K))
    (hk : ∃ k : ℕ, φ ^ 5 ^ k = 1) :
    ∃ q ∈ Λ₁ ⊔ Λ₂, ∀ g : K, φ g = q * g * q⁻¹ := by
  obtain ⟨k, hk⟩ := hk
  have hno : ¬ 5 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) :=
    hX.noOuter K hK
  have hmax := hXe.gammaMax K hK S
  obtain ⟨-, ⟨eK⟩⟩ := hK
  have hinner : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner K := by
    let π : MulAut K →* CFSG.ComponentClassification.OuterAutomorphisms.Outer K :=
      QuotientGroup.mk' _
    have hπ : π φ ^ 5 ^ k = 1 := by rw [← map_pow, hk, map_one]
    have hord : orderOf (π φ) ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one hπ
    have hord2 : orderOf (π φ) ∣
        Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) :=
      orderOf_dvd_natCard _
    by_contra hnot
    have hne : π φ ≠ 1 := fun h1 =>
      hnot ((QuotientGroup.eq_one_iff
        (N := CFSG.ComponentClassification.OuterAutomorphisms.inner K) φ).mp h1)
    have hord1 : orderOf (π φ) ≠ 1 := fun h1 => hne (orderOf_eq_one_iff.mp h1)
    obtain ⟨i, -, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hord
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hord1 (by simpa using hi')
    apply hno
    rw [hi'] at hord2
    exact (dvd_pow_self 5 hi0).trans hord2
  obtain ⟨q, rfl⟩ : ∃ q : K, MulAut.conj q = φ := hinner
  have hqN : q ∈ Subgroup.normalizer ((A10Gamma K (S : Subgroup K) : Subgroup K) : Set K) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hφ
  have hqΓ : q ∈ A10Gamma K (S : Subgroup K) := by
    rcases hmax (Subgroup.normalizer ((A10Gamma K (S : Subgroup K) : Subgroup K) : Set K))
        Subgroup.le_normalizer with hn | hn
    · rwa [hn] at hqN
    · haveI : (A10Gamma K (S : Subgroup K)).Normal := Subgroup.normalizer_eq_top_iff.mp hn
      haveI : IsSimpleGroup (alternatingGroup (Fin 10)) := alternatingGroup.isSimpleGroup (by simp)
      haveI : IsSimpleGroup K := eK.isSimpleGroup
      obtain ⟨e₁⟩ := h.iso₁
      have hΛ₁ne : Λ₁ ≠ ⊥ := (Subgroup.isSimpleGroup_iff.mp e₁.isSimpleGroup).1
      rcases Subgroup.Normal.eq_bot_or_eq_top (A10Gamma K (S : Subgroup K)) with h1 | h1
      · exact absurd (le_bot_iff.mp (h1 ▸ h.le_gamma₁)) hΛ₁ne
      · rw [h1]; trivial
  have hq5 : q ^ 5 ^ k = 1 := by
    have h1 : MulAut.conj (q ^ 5 ^ k) = 1 := by rw [map_pow]; exact hk
    generalize q ^ 5 ^ k = z at h1 ⊢
    refine a10t1_gf_centreless (by norm_num) eK z (fun g => ?_)
    have h2 := congrArg (fun f : MulAut K => f g) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc z * g = z * g * z⁻¹ * z := by group
      _ = g * z := by rw [h2]
  refine ⟨q, h.five q hqΓ ⟨k, hq5⟩, fun g => ?_⟩
  simp [MulAut.conj_apply]

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
