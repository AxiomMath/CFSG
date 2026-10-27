module

public import CFSG.Quasithin.Background.BlueprintB2Frattini
public import CFSG.Assembly.Defs

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup

variable {G : Type*} [Group G]

@[expose] def cj (Y : Subgroup G) (g : G) : Subgroup G := Y.map (MulAut.conj g⁻¹).toMonoidHom

section cj

variable {Y Y' : Subgroup G} {g h x : G}

theorem mem_cj : x ∈ cj Y g ↔ g * x * g⁻¹ ∈ Y := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    simp [mul_assoc]

theorem mem_cj_of_mem (hx : x ∈ Y) : g⁻¹ * x * g ∈ cj Y g := by
  rw [mem_cj]; simpa [mul_assoc] using hx

theorem cj_mono (h : Y ≤ Y') : cj Y g ≤ cj Y' g := Subgroup.map_mono h

theorem cj_sup : cj (Y ⊔ Y') g = cj Y g ⊔ cj Y' g := Subgroup.map_sup _ _ _

theorem cj_inf : cj (Y ⊓ Y') g = cj Y g ⊓ cj Y' g :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective

theorem cj_commutator : cj ⁅Y, Y'⁆ g = ⁅cj Y g, cj Y' g⁆ := Subgroup.map_commutator _ _ _

theorem cj_cj : cj (cj Y g) h = cj Y (g * h) := by
  ext x
  simp only [mem_cj, mul_inv_rev]
  simp [mul_assoc]

@[simp] theorem cj_one : cj Y (1 : G) = Y := by
  ext x; simp [mem_cj]

theorem cj_inv_cj : cj (cj Y g) g⁻¹ = Y := by
  rw [cj_cj]; simp

theorem cj_cj_inv : cj (cj Y g⁻¹) g = Y := by
  rw [cj_cj]; simp

theorem card_cj : Nat.card (cj Y g) = Nat.card Y :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem cj_eq_self_of_normal [Y.Normal] : cj Y g = Y := by
  ext x
  rw [mem_cj]
  constructor
  · intro h
    have := (inferInstance : Y.Normal).conj_mem _ h g⁻¹
    simpa [mul_assoc] using this
  · intro h
    exact (inferInstance : Y.Normal).conj_mem _ h g

theorem cj_bot : cj (⊥ : Subgroup G) g = ⊥ := by
  ext x; simp [mem_cj]

end cj

@[expose] def aimg (S : Subgroup G) (α : S ≃* S) (Y : Subgroup G) : Subgroup G :=
  ((Y.subgroupOf S).map α.toMonoidHom).map S.subtype

section aimg

variable {S : Subgroup G} {α : S ≃* S} {Y Y' : Subgroup G}

theorem mem_aimg {x : G} :
    x ∈ aimg S α Y ↔ ∃ y : S, (y : G) ∈ Y ∧ ((α y : S) : G) = x := by
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩

theorem aimg_le : aimg S α Y ≤ S := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := mem_aimg.mp hx
  exact (α y).2

theorem mem_aimg_of_mem {y : S} (hy : (y : G) ∈ Y) : ((α y : S) : G) ∈ aimg S α Y :=
  mem_aimg.mpr ⟨y, hy, rfl⟩

theorem aimg_mono (h : Y ≤ Y') : aimg S α Y ≤ aimg S α Y' := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_aimg.mp hx
  exact mem_aimg.mpr ⟨y, h hy, rfl⟩

theorem aimg_inf_self : aimg S α (Y ⊓ S) = aimg S α Y := by
  apply le_antisymm
  · exact aimg_mono inf_le_left
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_aimg.mp hx
    exact mem_aimg.mpr ⟨y, ⟨hy, y.2⟩, rfl⟩

theorem mem_aimg_symm_iff {x : G} (hx : x ∈ S) :
    x ∈ aimg S α Y ↔ ((α.symm ⟨x, hx⟩ : S) : G) ∈ Y := by
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := mem_aimg.mp h
    have : α y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [← this, α.symm_apply_apply]
    exact hy
  · intro h
    exact mem_aimg.mpr ⟨α.symm ⟨x, hx⟩, h, by simp⟩

theorem aimg_aimg_symm (hY : Y ≤ S) : aimg S α (aimg S α.symm Y) = Y := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_aimg.mp hx
    obtain ⟨z, hz, hzy⟩ := mem_aimg.mp hy
    have h1 : α.symm z = y := Subtype.ext hzy
    have h2 : α y = z := by rw [← h1]; exact α.apply_symm_apply z
    rw [h2]; exact hz
  · intro x hx
    refine mem_aimg.mpr ⟨α.symm ⟨x, hY hx⟩, mem_aimg.mpr ⟨⟨x, hY hx⟩, hx, rfl⟩, ?_⟩
    simp

theorem aimg_symm_aimg (hY : Y ≤ S) : aimg S α.symm (aimg S α Y) = Y := by
  simpa using aimg_aimg_symm (α := α.symm) hY

theorem aimg_self : aimg S α S = S := by
  apply le_antisymm aimg_le
  intro x hx
  exact mem_aimg.mpr ⟨α.symm ⟨x, hx⟩, (α.symm ⟨x, hx⟩).2, by simp⟩

theorem aimg_bot : aimg S α ⊥ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_aimg.mp hx
  have : y = 1 := Subtype.ext (Subgroup.mem_bot.mp hy)
  subst this
  simp

theorem exists_map_subtype (hY : Y ≤ S) : ∃ A : Subgroup S, A.map S.subtype = Y :=
  ⟨Y.subgroupOf S, Subgroup.map_subgroupOf_eq_of_le hY⟩

theorem aimg_map_subtype (A : Subgroup S) :
    aimg S α (A.map S.subtype) = (A.map α.toMonoidHom).map S.subtype := by
  unfold aimg
  have : (A.map S.subtype).subgroupOf S = A :=
    Subgroup.comap_map_eq_self_of_injective S.subtype_injective A
  rw [this]

theorem aimg_sup (hY : Y ≤ S) (hY' : Y' ≤ S) :
    aimg S α (Y ⊔ Y') = aimg S α Y ⊔ aimg S α Y' := by
  obtain ⟨A, rfl⟩ := exists_map_subtype hY
  obtain ⟨A', rfl⟩ := exists_map_subtype hY'
  rw [← Subgroup.map_sup, aimg_map_subtype, aimg_map_subtype, aimg_map_subtype,
    ← Subgroup.map_sup, ← Subgroup.map_sup]

theorem aimg_inf (hY : Y ≤ S) (hY' : Y' ≤ S) :
    aimg S α (Y ⊓ Y') = aimg S α Y ⊓ aimg S α Y' := by
  obtain ⟨A, rfl⟩ := exists_map_subtype hY
  obtain ⟨A', rfl⟩ := exists_map_subtype hY'
  rw [← Subgroup.map_inf_eq _ _ _ S.subtype_injective, aimg_map_subtype, aimg_map_subtype,
    aimg_map_subtype, ← Subgroup.map_inf_eq _ _ _ S.subtype_injective,
    ← Subgroup.map_inf_eq _ _ _ α.injective]

theorem aimg_commutator (hY : Y ≤ S) (hY' : Y' ≤ S) :
    aimg S α ⁅Y, Y'⁆ = ⁅aimg S α Y, aimg S α Y'⁆ := by
  obtain ⟨A, rfl⟩ := exists_map_subtype hY
  obtain ⟨A', rfl⟩ := exists_map_subtype hY'
  rw [← Subgroup.map_commutator, aimg_map_subtype, aimg_map_subtype, aimg_map_subtype,
    ← Subgroup.map_commutator, ← Subgroup.map_commutator]

theorem card_aimg (hY : Y ≤ S) : Nat.card (aimg S α Y) = Nat.card Y := by
  obtain ⟨A, rfl⟩ := exists_map_subtype hY
  rw [aimg_map_subtype, Subgroup.card_map_of_injective S.subtype_injective,
    Subgroup.card_map_of_injective S.subtype_injective,
    Subgroup.card_map_of_injective α.injective]

theorem subgroupOf_aimg (hY : Y ≤ S) :
    (aimg S α Y).subgroupOf S = (Y.subgroupOf S).map α.toMonoidHom := by
  obtain ⟨A, rfl⟩ := exists_map_subtype hY
  rw [aimg_map_subtype]
  have h1 : (A.map S.subtype).subgroupOf S = A :=
    Subgroup.comap_map_eq_self_of_injective S.subtype_injective A
  rw [h1]
  exact Subgroup.comap_map_eq_self_of_injective S.subtype_injective _

theorem normal_subgroupOf_aimg (hY : Y ≤ S) (hn : (Y.subgroupOf S).Normal) :
    ((aimg S α Y).subgroupOf S).Normal := by
  rw [subgroupOf_aimg hY]
  exact Subgroup.Normal.map hn α.toMonoidHom α.surjective

theorem aimg_centralizer (hY' : Y' ≤ S) :
    aimg S α (Y ⊓ Subgroup.centralizer (Y' : Set G)) =
      aimg S α Y ⊓ Subgroup.centralizer ((aimg S α Y' : Subgroup G) : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro hx
    obtain ⟨y, ⟨hyY, hyc⟩, rfl⟩ := mem_aimg.mp hx
    refine ⟨mem_aimg.mpr ⟨y, hyY, rfl⟩, ?_⟩
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_aimg.mp hz
    have h1 : (w : G) * y = y * w := hyc _ hw
    have h2 : w * y = y * w := Subtype.ext h1
    have h3 : α w * α y = α y * α w := by rw [← map_mul, ← map_mul, h2]
    exact congrArg Subtype.val h3
  · rintro ⟨hx, hc⟩
    obtain ⟨y, hyY, rfl⟩ := mem_aimg.mp hx
    refine mem_aimg.mpr ⟨y, ⟨hyY, ?_⟩, rfl⟩
    intro z hz
    have hzS : z ∈ S := hY' hz
    have h1 := hc _ (mem_aimg.mpr ⟨⟨z, hzS⟩, hz, rfl⟩)
    have h2 : α ⟨z, hzS⟩ * α y = α y * α ⟨z, hzS⟩ := Subtype.ext h1
    have h3 : (⟨z, hzS⟩ : S) * y = y * ⟨z, hzS⟩ := by
      apply α.injective
      rw [map_mul, map_mul]; exact h2
    exact congrArg Subtype.val h3

end aimg

section SylowTranslate

open CFSG.Quasithin.BlueprintB2

open scoped commutatorElement in
theorem commutator_normalClosure_mem {Q E A : Subgroup G} [E.Normal]
    (h : ∀ g : G, ∀ q ∈ Q, ∀ a ∈ cj A g, ⁅q, a⁆ ∈ E) :
    ∀ q ∈ Q, ∀ x ∈ Subgroup.normalClosure (A : Set G), ⁅q, x⁆ ∈ E := by
  intro q hq x hx
  have hx' : x ∈ Subgroup.closure (Group.conjugatesOfSet (A : Set G)) := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hc
    refine h c⁻¹ q hq _ ?_
    rw [mem_cj]
    simpa [mul_assoc] using ha
  | one => simp [commutatorElement_def]
  | mul x y _ _ ihx ihy =>
    have h1 : ⁅q, x * y⁆ = ⁅q, x⁆ * (x * ⁅q, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact mul_mem ihx ((inferInstance : E.Normal).conj_mem _ ihy x)
  | inv x _ ih =>
    have h1 : ⁅q, x⁻¹⁆ = x⁻¹ * ⁅q, x⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact (inferInstance : E.Normal).conj_mem _ (inv_mem ih) x⁻¹

theorem sylow_translate_core_aux {p : ℕ} [Fact p.Prime] [Finite G]
    {Q : Subgroup G} [Q.Normal] (hQ : IsPGroup p Q) {S₀ : Subgroup G} (hQS : Q ≤ S₀)
    (hgen : ⨆ g : G, cj S₀ g = ⊤)
    {V : Subgroup G} (hVS : V ≤ S₀)
    (hVn : (V.subgroupOf S₀).Normal) (hV : CFSG.IsElementaryAbelian p V)
    (hSV : ⁅S₀, V⁆ ≤ Subgroup.centralizer (S₀ : Set G))
    (α : S₀ ≃* S₀) (hα : S₀ = Q ⊔ aimg S₀ α V) :
    ⁅Q, pPrimeGen p (⊤ : Subgroup G)⁆ ≤ centerTorsion p Q ∧
      CFSG.IsElementaryAbelian p (⁅Q, pPrimeGen p (⊤ : Subgroup G)⁆ : Subgroup G) ∧
      ⁅Q, pPrimeGen p (⊤ : Subgroup G)⁆ ≤ Subgroup.centralizer (Q : Set G) := by
  open scoped commutatorElement in
  classical
  have hAn : ((aimg S₀ α V).subgroupOf S₀).Normal := normal_subgroupOf_aimg hVS hVn
  have hApow : ∀ a ∈ aimg S₀ α V, a ^ p = 1 := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := mem_aimg.mp ha
    have hy1 : (y : G) ^ p = 1 := (isElementaryAbelian_iff.mp hV).2 _ hy
    have hy2 : y ^ p = 1 := Subtype.ext (by simpa using hy1)
    have : (α y) ^ p = 1 := by rw [← map_pow, hy2, map_one]
    simpa using congrArg Subtype.val this
  have hSA : ⁅S₀, aimg S₀ α V⁆ ≤ Subgroup.centralizer (S₀ : Set G) := by
    have h1 : ⁅S₀, aimg S₀ α V⁆ = aimg S₀ α ⁅S₀, V⁆ := by
      rw [aimg_commutator le_rfl hVS, aimg_self]
    rw [h1]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_aimg.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h2 : ((α.symm ⟨s, hs⟩ : S₀) : G) * y = y * (α.symm ⟨s, hs⟩ : S₀) :=
      Subgroup.mem_centralizer_iff.mp (hSV hy) _ (α.symm ⟨s, hs⟩).2
    have h3 : (α.symm ⟨s, hs⟩ : S₀) * y = y * (α.symm ⟨s, hs⟩ : S₀) := Subtype.ext h2
    have h4 : (⟨s, hs⟩ : S₀) * α y = α y * ⟨s, hs⟩ := by
      have := congrArg α h3
      simpa using this
    exact congrArg Subtype.val h4
  have hEn : (centerTorsion p Q).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨hnQ, hnc, hnp⟩ := mem_centerTorsion_iff.mp hn
    rw [mem_centerTorsion_iff]
    refine ⟨(inferInstance : Q.Normal).conj_mem _ hnQ g, fun k hk => ?_, ?_⟩
    · have h1 := (inferInstance : Q.Normal).conj_mem k hk g⁻¹
      have h2 := hnc _ h1
      calc k * (g * n * g⁻¹) = g * ((g⁻¹ * k * g⁻¹⁻¹) * n) * g⁻¹ := by group
        _ = g * (n * (g⁻¹ * k * g⁻¹⁻¹)) * g⁻¹ := by rw [h2]
        _ = (g * n * g⁻¹) * k := by group
    · rw [conj_pow, hnp]; simp
  have hQA : ∀ q ∈ Q, ∀ a ∈ aimg S₀ α V, ⁅q, a⁆ ∈ centerTorsion p Q := by
    intro q hq a ha
    have hqS : q ∈ S₀ := hQS hq
    have haS : a ∈ S₀ := aimg_le ha
    have hqQ : ⁅q, a⁆ ∈ Q := by
      have := (inferInstance : Q.Normal).conj_mem q⁻¹ (inv_mem hq) a
      simpa [commutatorElement_def, mul_assoc] using mul_mem hq this
    have hqA : ⁅q, a⁆ ∈ aimg S₀ α V := by
      have h1 := hAn.conj_mem ⟨a, haS⟩ ha ⟨q, hqS⟩
      have h2 : q * a * q⁻¹ ∈ aimg S₀ α V := h1
      have := mul_mem h2 (inv_mem ha)
      simpa [commutatorElement_def, mul_assoc] using this
    have hcomm : ⁅q, a⁆ ∈ Subgroup.centralizer (S₀ : Set G) :=
      hSA (Subgroup.commutator_mem_commutator hqS ha)
    exact mem_centerTorsion_iff.mpr ⟨hqQ, fun k hk => Subgroup.mem_centralizer_iff.mp hcomm k
      (hQS hk), hApow _ hqA⟩
  have hQAE : ∀ g : G, ∀ q ∈ Q, ∀ a ∈ cj (aimg S₀ α V) g, ⁅q, a⁆ ∈ centerTorsion p Q := by
    intro g q hq a ha
    have h1 := hQA (g * q * g⁻¹) ((inferInstance : Q.Normal).conj_mem q hq g) (g * a * g⁻¹)
      (mem_cj.mp ha)
    have h2 := hEn.conj_mem _ h1 g⁻¹
    have h3 : g⁻¹ * ⁅g * q * g⁻¹, g * a * g⁻¹⁆ * g⁻¹⁻¹ = ⁅q, a⁆ := by
      simp only [commutatorElement_def]; group
    rwa [h3] at h2
  have hHE := commutator_normalClosure_mem (Q := Q) (E := centerTorsion p Q)
    (A := aimg S₀ α V) hQAE
  have hSN : S₀ ≤ Q ⊔ Subgroup.normalClosure (aimg S₀ α V : Set G) := by
    exact hα.le.trans (sup_le_sup_left Subgroup.le_normalClosure Q)
  have htop : Q ⊔ Subgroup.normalClosure (aimg S₀ α V : Set G) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine iSup_le fun g => ?_
    intro x hx
    rw [mem_cj] at hx
    have h1 : g * x * g⁻¹ ∈ Q ⊔ Subgroup.normalClosure (aimg S₀ α V : Set G) := hSN hx
    have h2 := (inferInstance : (Q ⊔ Subgroup.normalClosure (aimg S₀ α V : Set G)).Normal).conj_mem
      _ h1 g⁻¹
    simpa [mul_assoc] using h2
  have hKN : pPrimeGen p (⊤ : Subgroup G) ≤ Subgroup.normalClosure (aimg S₀ α V : Set G) := by
    refine pPrimeGen_le_of_pow_mem fun x _ => ?_
    have hx : x ∈ Q ⊔ Subgroup.normalClosure (aimg S₀ α V : Set G) := htop ▸ Subgroup.mem_top x
    obtain ⟨q, hq, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
    refine ⟨k, ?_⟩
    have hk' : q ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hn1 : QuotientGroup.mk' (Subgroup.normalClosure (aimg S₀ α V : Set G)) n = 1 :=
      (QuotientGroup.eq_one_iff n).mpr hn
    have : QuotientGroup.mk' (Subgroup.normalClosure (aimg S₀ α V : Set G))
        ((q * n) ^ p ^ k) = 1 := by
      rw [map_pow, map_mul, hn1, mul_one, ← map_pow, hk', map_one]
    exact (QuotientGroup.eq_one_iff _).mp this
  have hQK : ⁅Q, pPrimeGen p (⊤ : Subgroup G)⁆ ≤ centerTorsion p Q :=
    Subgroup.commutator_le.mpr fun q hq k hk => hHE q hq k (hKN hk)
  refine ⟨hQK, ?_, ?_⟩
  · refine isElementaryAbelian_iff.mpr ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨haQ, -, -⟩ := mem_centerTorsion_iff.mp (hQK ha)
      obtain ⟨-, hbc, -⟩ := mem_centerTorsion_iff.mp (hQK hb)
      exact hbc a haQ
    · exact (mem_centerTorsion_iff.mp (hQK ha)).2.2
  · intro x hx
    obtain ⟨-, hxc, -⟩ := mem_centerTorsion_iff.mp (hQK hx)
    exact Subgroup.mem_centralizer_iff.mpr fun k hk => hxc k hk

theorem sylow_module_translate_centralizes_core {p : ℕ} [Fact p.Prime] [Finite G]
    {Q : Subgroup G} [Q.Normal] (hQ : IsPGroup p Q) (S : Sylow p G)
    (hgen : ⨆ g : G, cj (S : Subgroup G) g = ⊤)
    {V : Subgroup G} (hVS : V ≤ (S : Subgroup G))
    (hVn : (V.subgroupOf (S : Subgroup G)).Normal) (hV : CFSG.IsElementaryAbelian p V)
    (hSV : ⁅(S : Subgroup G), V⁆ ≤ Subgroup.centralizer ((S : Subgroup G) : Set G))
    (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hα : (S : Subgroup G) = Q ⊔ aimg (S : Subgroup G) α V) :
    ⁅Q, pPrimeGen p (⊤ : Subgroup G)⁆ ≤ centerTorsion p Q ∧
      CFSG.IsElementaryAbelian p (⁅Q, pPrimeGen p (⊤ : Subgroup G)⁆ : Subgroup G) ∧
      ⁅Q, pPrimeGen p (⊤ : Subgroup G)⁆ ≤ Subgroup.centralizer (Q : Set G) :=
  sylow_translate_core_aux hQ (hQ.le_sylow_of_normal S) hgen hVS hVn hV hSV α hα

end SylowTranslate

end CFSG.QuasithinUnique.Setup.Campbell
