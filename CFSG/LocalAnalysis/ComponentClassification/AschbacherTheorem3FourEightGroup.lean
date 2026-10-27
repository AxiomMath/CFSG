module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open

variable {X : Type} [Group X] [Finite X]

theorem eq_of_sq_mem {G T N : Subgroup X} (hT : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (G : Set X)) (hGT : ⁅T, G⁆ = G) (hNG : N ≤ G)
    (hsq : ∀ x ∈ G, x ^ 2 ∈ N) : N = G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s : Set X := {z | ∃ x ∈ G, x ^ 2 = z} with hs
  set N₂ : Subgroup X := Subgroup.closure s with hN₂
  have hN₂N : N₂ ≤ N := by
    rw [hN₂, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hsq x hx
  apply le_antisymm hNG
  suffices hG : G ≤ N₂ from hG.trans hN₂N
  have hnorm : ∀ c ∈ Subgroup.normalizer (G : Set X), c ∈ Subgroup.normalizer (N₂ : Set X) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hN₂, MonoidHom.map_closure]
    congr 1
    ext z
    simp only [Set.mem_image, hs, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨c * x * c⁻¹, (Subgroup.mem_normalizer_iff.mp hc x).mp hx, ?_⟩
      exact (by rw [pow_two, pow_two]; group : (c * x * c⁻¹) ^ 2 = c * x ^ 2 * c⁻¹)
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(c⁻¹ * x * c) ^ 2, ⟨c⁻¹ * x * c, ?_, rfl⟩, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hc) x).mp hx
        simpa using this
      · exact (by rw [pow_two, pow_two]; group : c * (c⁻¹ * x * c) ^ 2 * c⁻¹ = x ^ 2)
  have hGTN : G ⊔ T ≤ Subgroup.normalizer (N₂ : Set X) :=
    fun c hc => hnorm c (sup_le Subgroup.le_normalizer hTN hc)
  set L := G ⊔ T with hL
  have hN₂L : N₂ ≤ L := (hN₂N.trans hNG).trans le_sup_left
  set M : Subgroup L := N₂.subgroupOf L with hM
  have hMn : M.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hN₂L).mpr hGTN
  set π := QuotientGroup.mk' M with hπ
  set G' := G.subgroupOf L with hG'
  set T' := T.subgroupOf L with hT'
  set Gb := G'.map π with hGb
  set Tb := T'.map π with hTb
  have hGb2 : IsPGroup 2 Gb := by
    rintro ⟨_, ⟨g, hg, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hM,
      Subgroup.mem_subgroupOf]
    exact Subgroup.subset_closure ⟨(g : X), hg, by simp⟩
  have hTb2 : IsPGroup 2 Tb := (hT.comap_subtype).map π
  have hT'N : T' ≤ Subgroup.normalizer (G' : Set L) := by
    intro x hx
    rw [hG', ← Subgroup.subgroupOf_normalizer_eq (le_sup_left : G ≤ L)]
    exact hTN hx
  have hTbN : Tb ≤ Subgroup.normalizer (Gb : Set (L ⧸ M)) :=
    (Subgroup.map_mono hT'N).trans (Subgroup.le_normalizer_map _)
  by_contra hne
  have hGbne : Gb ≠ ⊥ := by
    intro hbot
    apply hne
    intro x hx
    have h1 : π ⟨x, (le_sup_left : G ≤ L) hx⟩ ∈ Gb := Subgroup.mem_map_of_mem π hx
    rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hM,
      Subgroup.mem_subgroupOf] at h1
    exact h1
  have hlt := CFSG.GorensteinWalter.SchurZassenhaus.commutator_lt_of_pGroups Gb Tb hGb2 hTb2
    hTbN hGbne
  have heq : ⁅Gb, Tb⁆ = Gb := by
    rw [hGb, hTb, ← Subgroup.map_commutator]
    congr 1
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, hG', hT', Subgroup.map_subgroupOf_eq_of_le le_sup_left,
      Subgroup.map_subgroupOf_eq_of_le le_sup_right, Subgroup.commutator_comm, hGT]
  rw [heq] at hlt
  exact lt_irrefl _ hlt

theorem false_of_relIndex_two_mul_odd {G T N : Subgroup X} (hT : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (G : Set X)) (hGT : ⁅T, G⁆ = G) (hNG : N ≤ G)
    (hNn : G ≤ Subgroup.normalizer (N : Set X)) (h2 : 2 ∣ N.relIndex G)
    (h4 : ¬ 4 ∣ N.relIndex G) : False := by
  have hN' : (N.subgroupOf G).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNG).mpr hNn
  obtain ⟨M₂, hM₂n, hM₂idx, -⟩ :=
    CFSG.GorensteinWalter.exists_normal_index_two_containing_of_index_eq_two_mul_odd hN' h2 h4
  have hsq : ∀ x ∈ G, x ^ 2 ∈ M₂.map G.subtype := by
    intro x hx
    have := Subgroup.sq_mem_of_index_two hM₂idx (⟨x, hx⟩ : G)
    exact ⟨_, this, rfl⟩
  have heq := eq_of_sq_mem hT hTN hGT (Subgroup.map_subtype_le M₂) hsq
  have htop : M₂ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (x : X) ∈ M₂.map G.subtype := by rw [heq]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← Subtype.ext hyx]
  rw [htop, Subgroup.index_top] at hM₂idx
  omega

theorem isSylowOf_exists_conj_mem {p : ℕ} [Fact p.Prime] {P K H : Subgroup X}
    (hP : IsSylowOf p P K) (hHK : H ≤ K) (hH : IsPGroup p H) :
    ∃ k ∈ K, ∀ h ∈ H, k⁻¹ * h * k ∈ P := by
  have hH' : IsPGroup p (H.subgroupOf K) := hH.comap_subtype
  obtain ⟨Q, hQ⟩ := hH'.exists_le_sylow
  have hQs : IsSylowOf p ((Q : Subgroup K).map K.subtype) K := ⟨Q, rfl⟩
  obtain ⟨k, hk, hkey⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hP hQs
  refine ⟨k, hk, fun h hh => ?_⟩
  apply (hkey h).mp
  exact ⟨⟨h, hHK hh⟩, hQ hh, rfl⟩

theorem isSylowOf_rightConjugate {p : ℕ} [Fact p.Prime] {P K : Subgroup X}
    (hP : IsSylowOf p P K) {y : X} (hy : y ∈ K) :
    IsSylowOf p (AschbacherTightEmbedding.rightConjugate P y) K := by
  apply isSylowOf_of_card
  · intro x hx
    rw [mem_rightConjugate_iff] at hx
    have := K.mul_mem (K.mul_mem (K.inv_mem hy) (hP.le hx)) hy
    simpa [mul_assoc] using this
  · rw [rightConjugate_card, CFSG.ABGLocalTools.IsSylowOf.card_eq hP]

theorem eq_of_elation {N E A S₀ : Subgroup X} (hEN : N ≤ Subgroup.normalizer (E : Set X))
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hAE : A ≤ E) {w : X}
    (hcoset : ∀ x ∈ E, x ∉ A → w⁻¹ * x ∈ A) (hS₀ : IsSylowOf 2 S₀ N)
    (hS₀A : ∀ s ∈ S₀, ∀ a ∈ A, s * a = a * s) {y : X} (hy : y ∈ N) {a s : X} (ha : a ∈ A)
    (hay : a ∈ AschbacherTightEmbedding.rightConjugate A y) (hs : s ∈ S₀)
    (hws : s⁻¹ * w * s = w * a) :
    AschbacherTightEmbedding.rightConjugate A y = A ∨ a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A' := AschbacherTightEmbedding.rightConjugate A y with hA'
  by_cases heq : A' = A
  · exact Or.inl heq
  right
  have hA'E : A' ≤ E := by
    intro x hx
    rw [hA', mem_rightConjugate_iff] at hx
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hEN hy)) _).mp (hAE hx)
    simpa [mul_assoc] using h1
  have hsA : ∀ x ∈ A, s⁻¹ * x * s = x := fun x hx => by
    rw [mul_assoc, ← hS₀A s hs x hx]; group
  have hsx : ∀ x ∈ E, x ∉ A → s⁻¹ * x * s = x * a := by
    intro x hxE hxA
    have hb := hcoset x hxE hxA
    have h1 : x = w * (w⁻¹ * x) := by group
    calc s⁻¹ * x * s = (s⁻¹ * w * s) * (s⁻¹ * (w⁻¹ * x) * s) := by
          conv_lhs => rw [h1]
          group
      _ = w * a * (w⁻¹ * x) := by rw [hws, hsA _ hb]
      _ = w * ((w⁻¹ * x) * a) := by
          rw [mul_assoc w a, hEab a (hAE ha) _ (hAE hb)]
      _ = x * a := by group
  have hsN : s ∈ Subgroup.normalizer (A' : Set X) := by
    rw [← rightConjugate_eq_self_iff]
    apply Subgroup.eq_of_le_of_card_ge _ (rightConjugate_card A' s).ge
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    set x' := s * x * s⁻¹ with hx'
    have hx'E : x' ∈ E := hA'E hx
    have hxeq : x = s⁻¹ * x' * s := by rw [hx']; group
    rw [hxeq]
    by_cases hx'A : x' ∈ A
    · rw [hsA x' hx'A]; exact hx
    · rw [hsx x' hx'E hx'A]; exact A'.mul_mem hx hay
  set K := N ⊓ Subgroup.normalizer (A' : Set X) with hK
  set S₁ := AschbacherTightEmbedding.rightConjugate S₀ y with hS₁
  have hS₁N : IsSylowOf 2 S₁ N := isSylowOf_rightConjugate hS₀ hy
  have hS₁K : S₁ ≤ K := by
    refine le_inf hS₁N.le ?_
    intro t ht
    rw [hS₁, mem_rightConjugate_iff] at ht
    rw [← rightConjugate_eq_self_iff, hA', rightConjugate_mul]
    have h1 : y * t = (y * t * y⁻¹) * y := by group
    rw [h1, ← rightConjugate_mul]
    congr 1
    rw [rightConjugate_eq_self_iff]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
      (fun x hx => (hS₀A _ ht x hx).symm))
  have hS₁K' : IsSylowOf 2 S₁ K := hS₁N.of_le hS₁K inf_le_left
  have hsK : s ∈ K := ⟨hS₀.le hs, hsN⟩
  have hz : IsPGroup 2 (Subgroup.zpowers s) := hS₀.isPGroup.to_le
    (Subgroup.zpowers_le.mpr hs)
  obtain ⟨k, hk, hkey⟩ := isSylowOf_exists_conj_mem hS₁K' (Subgroup.zpowers_le.mpr hsK) hz
  have hks := hkey s (Subgroup.mem_zpowers s)
  have hcent : ∀ x ∈ A', s * x = x * s := by
    intro x hx
    have hkx : k⁻¹ * x * k ∈ A' := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk.2) x).mp hx
      simpa using this
    rw [hS₁, mem_rightConjugate_iff] at hks
    rw [hA', mem_rightConjugate_iff] at hkx
    have h1 := hS₀A _ hks _ hkx
    have h2 : y * (k⁻¹ * s * k) * y⁻¹ * (y * (k⁻¹ * x * k) * y⁻¹) =
        y * ((k⁻¹ * s * k) * (k⁻¹ * x * k)) * y⁻¹ := by group
    have h3 : y * (k⁻¹ * x * k) * y⁻¹ * (y * (k⁻¹ * s * k) * y⁻¹) =
        y * ((k⁻¹ * x * k) * (k⁻¹ * s * k)) * y⁻¹ := by group
    rw [h2, h3] at h1
    have h4 := mul_left_cancel (mul_right_cancel h1)
    calc s * x = k * ((k⁻¹ * s * k) * (k⁻¹ * x * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * x * k) * (k⁻¹ * s * k)) * k⁻¹ := by rw [h4]
      _ = x * s := by group
  have hnot : ¬ A' ≤ A := fun hle => heq (Subgroup.eq_of_le_of_card_ge hle
    (by rw [hA', rightConjugate_card]))
  obtain ⟨x, hxA', hxA⟩ := Set.not_subset.mp hnot
  have h1 := hsx x (hA'E hxA') hxA
  have h2 : s⁻¹ * x * s = x := by rw [mul_assoc, ← hcent x hxA']; group
  rw [h2] at h1
  exact (mul_eq_left.mp h1.symm)

theorem exists_normalizer_eq_rightConjugate {G₀ P E : Subgroup X} (hP : IsSylowOf 2 P G₀)
    (hE : P ≤ Subgroup.normalizer (E : Set X)) {x : X} (hx : x ∈ G₀)
    (hEx : P ≤ Subgroup.normalizer (AschbacherTightEmbedding.rightConjugate E x : Set X)) :
    ∃ n ∈ G₀ ⊓ Subgroup.normalizer (P : Set X),
      AschbacherTightEmbedding.rightConjugate E x =
        AschbacherTightEmbedding.rightConjugate E n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := G₀ ⊓ Subgroup.normalizer (E : Set X) with hK
  have hPK : IsSylowOf 2 P K := hP.of_le (le_inf hP.le hE) inf_le_left
  set P' := AschbacherTightEmbedding.rightConjugate P x⁻¹ with hP'
  have hP'K : IsSylowOf 2 P' K := by
    have h1 : IsSylowOf 2 P' G₀ := isSylowOf_rightConjugate hP (G₀.inv_mem hx)
    refine h1.of_le (le_inf h1.le ?_) inf_le_left
    intro z hz
    rw [hP', mem_rightConjugate_iff, inv_inv] at hz
    have h2 : AschbacherTightEmbedding.rightConjugate
        (AschbacherTightEmbedding.rightConjugate E x) (x⁻¹ * z * x) =
        AschbacherTightEmbedding.rightConjugate E x := (rightConjugate_eq_self_iff _ _).mpr (hEx hz)
    rw [← rightConjugate_eq_self_iff]
    have h3 : z = x * (x⁻¹ * z * x) * x⁻¹ := by group
    rw [h3, ← rightConjugate_mul, ← rightConjugate_mul, h2, rightConjugate_mul, mul_inv_cancel,
      rightConjugate_one]
  obtain ⟨k, hk, hkey⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hPK hP'K
  refine ⟨k⁻¹ * x, ⟨G₀.mul_mem (G₀.inv_mem hk.1) hx, ?_⟩, ?_⟩
  · show k⁻¹ * x ∈ Subgroup.normalizer (P : Set X)
    rw [← rightConjugate_eq_self_iff]
    ext z
    rw [mem_rightConjugate_iff]
    have h1 := hkey (x * z * x⁻¹)
    rw [hP', mem_rightConjugate_iff, inv_inv] at h1
    have h2 : x⁻¹ * (x * z * x⁻¹) * x = z := by group
    rw [h2] at h1
    have h3 : k⁻¹ * x * z * (k⁻¹ * x)⁻¹ = k⁻¹ * (x * z * x⁻¹) * k := by group
    rw [h3]
    exact h1.symm
  · rw [← rightConjugate_mul]
    congr 1
    exact ((rightConjugate_eq_self_iff _ _).mpr (Subgroup.inv_mem _ hk.2)).symm

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
