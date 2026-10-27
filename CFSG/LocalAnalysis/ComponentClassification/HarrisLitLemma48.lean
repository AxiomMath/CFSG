module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma42B

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

theorem card_eq_of_conj_iff {G : Type*} [Group G] {A B : Subgroup G} (c : G)
    (h : ∀ x, x ∈ A ↔ c⁻¹ * x * c ∈ B) : Nat.card A = Nat.card B := by
  have hA : A = B.map (MulAut.conj c).toMonoidHom := by
    ext x
    rw [h, Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨c⁻¹ * x * c, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
  rw [hA, Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem mem_normalizer_of_conj_le {G : Type*} [Group G] [Finite G] {A : Subgroup G} {g : G}
    (h : ∀ x ∈ A, g * x * g⁻¹ ∈ A) : g ∈ normalizer (A : Set G) := by
  have hmap : A.map (MulAut.conj g).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge
      (by
        rintro _ ⟨x, hx, rfl⟩
        simpa [MulAut.conj_apply] using h x hx)
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← hmap] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := (MulAut.conj g).injective (by simpa [MulAut.conj_apply] using hyx)
  rwa [← this]

theorem exists_isSylowOf_ge {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup G} (hP : IsPGroup p P) (hPK : P ≤ K) :
    ∃ Q : Subgroup G, IsSylowOf p Q K ∧ P ≤ Q := by
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype : IsPGroup p (P.subgroupOf K)).exists_le_sylow
  exact ⟨_, ⟨Q, rfl⟩, fun x hx => ⟨⟨x, hPK hx⟩, hQ hx, rfl⟩⟩

theorem le_normalizer_of_card_le_two_mul {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hAB : A ≤ B) (hcard : Nat.card B ≤ 2 * Nat.card A) : B ≤ normalizer (A : Set G) := by
  rw [← normal_subgroupOf_iff_le_normalizer hAB]
  have hi := (A.subgroupOf B).index_mul_card
  have hcA : Nat.card (A.subgroupOf B) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  rw [hcA] at hi
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hle : (A.subgroupOf B).index ≤ 2 := by
    by_contra hlt
    have : 3 * Nat.card A ≤ (A.subgroupOf B).index * Nat.card A :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hne : (A.subgroupOf B).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases Nat.lt_or_ge (A.subgroupOf B).index 2 with hlt | hge
  · have h1 : (A.subgroupOf B).index = 1 := by omega
    rw [Subgroup.index_eq_one] at h1
    rw [h1]
    infer_instance
  · exact Subgroup.normal_of_index_eq_two (by omega)

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem sylow_transport [Finite X] (hσ : Setup42 h hS w z) {S' : Subgroup X}
    (hS' : IsSylowOf 2 S' (centralizer ({t} : Set X)))
    (hTS' : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ S') :
    S' ⊓ L = S ⊓ L ∧
      S' ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) = closure {t, w ^ (orderOf w / 2), z} ∧
      S' ⊓ centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) =
        zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ∧
      ∀ F : Subgroup X, F ≤ S' → (∀ g ∈ S ⊓ L, ∀ x ∈ F, g * x * g⁻¹ ∈ F) →
        (∀ x ∈ F, x ^ 2 = 1) → F ≤ closure {t, w ^ (orderOf w / 2), z} := by
  have hDT : S ⊓ L ≤ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := le_sup_left.trans' le_sup_right
  have hXT := hσ.X_le_T
  have hDD : S' ⊓ L = S ⊓ L :=
    (h.isSylowOf_inf hS).eq_of_le (le_inf (hDT.trans hTS') inf_le_right) inf_le_right
      (hS'.isPGroup.to_le inf_le_left)
  obtain ⟨c, hcH, hc⟩ := hS.exists_mem_conj hS'
  have hcL : ∀ x, x ∈ L ↔ c⁻¹ * x * c ∈ L := by
    intro x
    simpa using mem_normalizer_iff.mp (inv_mem (h.centralizer_le_normalizer hcH)) x
  have hcD : ∀ x, x ∈ S ⊓ L ↔ c⁻¹ * x * c ∈ S ⊓ L := by
    intro x
    constructor
    · intro hx
      rw [← hDD] at hx
      exact ⟨(hc x).mp hx.1, (hcL x).mp hx.2⟩
    · intro hx
      rw [← hDD]
      exact ⟨(hc x).mpr hx.1, (hcL x).mpr hx.2⟩
  have hcD' : ∀ d ∈ S ⊓ L, c * d * c⁻¹ ∈ S ⊓ L := fun d hd =>
    (hcD _).mpr (by simpa [mul_assoc] using hd)
  have hcY : ∀ x, x ∈ S' ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) ↔
      c⁻¹ * x * c ∈ S ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) := by
    intro x
    constructor
    · rintro ⟨hx, hxc⟩
      refine ⟨(hc x).mp hx, mem_centralizer_iff.mpr fun d hd => ?_⟩
      have := mem_centralizer_iff.mp hxc _ (hcD' d hd)
      calc d * (c⁻¹ * x * c) = c⁻¹ * ((c * d * c⁻¹) * x) * c := by group
        _ = c⁻¹ * (x * (c * d * c⁻¹)) * c := by rw [this]
        _ = c⁻¹ * x * c * d := by group
    · rintro ⟨hx, hxc⟩
      refine ⟨(hc x).mpr hx, mem_centralizer_iff.mpr fun d hd => ?_⟩
      have := mem_centralizer_iff.mp hxc _ ((hcD d).mp hd)
      calc d * x = c * ((c⁻¹ * d * c) * (c⁻¹ * x * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * x * c) * (c⁻¹ * d * c)) * c⁻¹ := by rw [this]
        _ = x * d := by group
  rw [hσ.centralizer_D] at hcY
  have hY : S' ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) =
      closure {t, w ^ (orderOf w / 2), z} := by
    refine (Subgroup.eq_of_le_of_card_ge (fun x hx => Subgroup.mem_inf.mpr ⟨hTS' (hXT hx), ?_⟩)
      (card_eq_of_conj_iff c hcY).le).symm
    rw [← hσ.centralizer_D] at hx
    exact hx.2
  have hcX : ∀ x, x ∈ closure {t, w ^ (orderOf w / 2), z} ↔
      c⁻¹ * x * c ∈ closure {t, w ^ (orderOf w / 2), z} := by
    intro x
    rw [← hcY, hY]
  have hcT : ∀ x, x ∈ S' ⊓
      centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) ↔
      c⁻¹ * x * c ∈ S ⊓
        centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) := by
    intro x
    constructor
    · rintro ⟨hx, hxc⟩
      refine ⟨(hc x).mp hx, mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hy' : c * y * c⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} :=
        (hcX _).mpr (by simpa [mul_assoc] using hy)
      have := mem_centralizer_iff.mp hxc _ hy'
      calc y * (c⁻¹ * x * c) = c⁻¹ * ((c * y * c⁻¹) * x) * c := by group
        _ = c⁻¹ * (x * (c * y * c⁻¹)) * c := by rw [this]
        _ = c⁻¹ * x * c * y := by group
    · rintro ⟨hx, hxc⟩
      refine ⟨(hc x).mpr hx, mem_centralizer_iff.mpr fun y hy => ?_⟩
      have := mem_centralizer_iff.mp hxc _ ((hcX y).mp hy)
      calc y * x = c * ((c⁻¹ * y * c) * (c⁻¹ * x * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * x * c) * (c⁻¹ * y * c)) * c⁻¹ := by rw [this]
        _ = x * y := by group
  rw [hσ.centralizer_X] at hcT
  have hTX : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤
      S' ⊓ centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) :=
    fun y hy => ⟨hTS' hy, mem_centralizer_iff.mpr fun x hx =>
      (mem_centralizer_iff.mp (hσ.X_le_center_T hx).2 y hy).symm⟩
  refine ⟨hDD, hY, (Subgroup.eq_of_le_of_card_ge hTX (card_eq_of_conj_iff c hcT).le).symm, ?_⟩
  intro F hFS' hFn hF2 x hx
  have hF' : F.map (MulAut.conj c⁻¹).toMonoidHom ≤ closure {t, w ^ (orderOf w / 2), z} := by
    refine hσ.le_X_of_normal_S ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using (hc y).mp (hFS' hy)
    · rintro d hd _ ⟨y, hy, rfl⟩
      refine ⟨(c * d * c⁻¹) * y * (c * d * c⁻¹)⁻¹, hFn _ (hcD' d hd) y hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show (c⁻¹ * y * c⁻¹⁻¹) ^ 2 = c⁻¹ * y ^ 2 * c by rw [sq, sq]; group, hF2 y hy,
        mul_one, inv_mul_cancel]
  have : c⁻¹ * x * c ∈ closure {t, w ^ (orderOf w / 2), z} :=
    hF' ⟨x, hx, by simp⟩
  exact (hcX x).mpr this

theorem exists_normalizer_conj_eq [Finite X] (hσ : Setup42 h hS w z) {F : Subgroup X}
    (hTF : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ F) {f : X} (hf : f ∈ F)
    (hfX : f * t * f⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z}) :
    ∃ g ∈ F, g ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) ∧
      g * t * g⁻¹ = f * t * f⁻¹ := by
  have hTS := hσ.T_le
  have hXT := hσ.X_le_T
  have hDT : S ⊓ L ≤ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := le_sup_left.trans' le_sup_right
  have hTH : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ centralizer ({t} : Set X) := hTS.trans hS.le
  have hTτ : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ centralizer ({f * t * f⁻¹} : Set X) :=
    fun g hg => mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (hσ.X_le_center_T hfX).2 g hg)
  have hT2 : IsPGroup 2 (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) := hS.isPGroup.to_le hTS
  obtain ⟨R, hR, hTR⟩ := exists_isSylowOf_ge hT2 (le_inf hTF hTH)
  obtain ⟨R₁, hR₁, hTR₁⟩ := exists_isSylowOf_ge hT2 (le_inf hTF hTτ)
  have hK : (F ⊓ centralizer ({t} : Set X)).map (MulAut.conj f).toMonoidHom =
      F ⊓ centralizer ({f * t * f⁻¹} : Set X) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, ⟨hyF, hyt⟩, rfl⟩
      refine ⟨F.mul_mem (F.mul_mem hf hyF) (F.inv_mem hf), ?_⟩
      calc f * y * f⁻¹ * (f * t * f⁻¹) = f * (y * t) * f⁻¹ := by group
        _ = f * (t * y) * f⁻¹ := by rw [hyt]
        _ = f * t * f⁻¹ * (f * y * f⁻¹) := by group
    · rintro ⟨hxF, hxt⟩
      refine ⟨f⁻¹ * x * f, ⟨F.mul_mem (F.mul_mem (F.inv_mem hf) hxF) hf, ?_⟩, by group⟩
      calc f⁻¹ * x * f * t = f⁻¹ * (x * (f * t * f⁻¹)) * f := by group
        _ = f⁻¹ * ((f * t * f⁻¹) * x) * f := by rw [hxt]
        _ = t * (f⁻¹ * x * f) := by group
  have hRf : IsSylowOf 2 (R.map (MulAut.conj f).toMonoidHom)
      (F ⊓ centralizer ({f * t * f⁻¹} : Set X)) := by
    rw [← hK]
    exact isSylowOf_map _ hR
  obtain ⟨k, hkB, hk⟩ := hR₁.exists_mem_conj hRf
  have hkτ : k * (f * t * f⁻¹) = f * t * f⁻¹ * k := mem_centralizer_singleton_iff.mp hkB.2
  have hgR : ∀ x, x ∈ R ↔ k⁻¹ * f * x * (k⁻¹ * f)⁻¹ ∈ R₁ := by
    intro x
    rw [show k⁻¹ * f * x * (k⁻¹ * f)⁻¹ = k⁻¹ * (f * x * f⁻¹) * k by group, ← hk]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := (MulAut.conj f).injective (by simpa [MulAut.conj_apply] using hyx)
      rwa [← this]
  have hgR' : ∀ x, x ∈ R₁ ↔ (k⁻¹ * f)⁻¹ * x * (k⁻¹ * f) ∈ R := by
    intro x
    rw [hgR, show k⁻¹ * f * ((k⁻¹ * f)⁻¹ * x * (k⁻¹ * f)) * (k⁻¹ * f)⁻¹ = x by group]
  have hgF : k⁻¹ * f ∈ F := F.mul_mem (F.inv_mem hkB.1) hf
  have hgt : k⁻¹ * f * t * (k⁻¹ * f)⁻¹ = f * t * f⁻¹ := by
    calc k⁻¹ * f * t * (k⁻¹ * f)⁻¹ = k⁻¹ * (f * t * f⁻¹ * k) := by group
      _ = k⁻¹ * (k * (f * t * f⁻¹)) := by rw [hkτ]
      _ = f * t * f⁻¹ := by group
  set g := k⁻¹ * f with hg
  obtain ⟨S'', hS'', hRS''⟩ := exists_isSylowOf_ge hR.isPGroup (hR.le.trans inf_le_right)
  obtain ⟨-, -, hCX, hEX⟩ := hσ.sylow_transport hS'' (hTR.trans hRS'')
  have hcardS : Nat.card S ≤ 2 * Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) :=
    (h.lemma41_of_lift hS hσ.lift hσ.gen3).2.2.2.2.1
  have hcardR : Nat.card R ≤ 2 * Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) := by
    calc Nat.card R ≤ Nat.card S'' := Subgroup.card_le_of_le hRS''
      _ = Nat.card S := by rw [hS''.card_eq, hS.card_eq]
      _ ≤ _ := hcardS
  have hcardR₁ : Nat.card R₁ = Nat.card R := card_eq_of_conj_iff g hgR'
  have hR₁N : R₁ ≤ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) :=
    le_normalizer_of_card_le_two_mul hTR₁ (hcardR₁ ▸ hcardR)
  have hXg : ∀ x ∈ closure {t, w ^ (orderOf w / 2), z},
      g⁻¹ * x * g⁻¹⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} := by
    intro x hx
    rw [inv_inv]
    have hE := hEX ((closure {t, w ^ (orderOf w / 2), z}).map (MulAut.conj g⁻¹).toMonoidHom)
      (by
        rintro _ ⟨y, hy, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        exact hRS'' ((hgR' y).mp (hTR₁ (hXT hy))))
      (by
        rintro d hd _ ⟨y, hy, rfl⟩
        have hgd : g * d * g⁻¹ ∈ R₁ := (hgR d).mp (hTR (hDT hd))
        have hgdN := hσ.normalizer_T_le_normalizer_X (hR₁N hgd)
        refine ⟨(g * d * g⁻¹) * y * (g * d * g⁻¹)⁻¹, (mem_normalizer_iff.mp hgdN y).mp hy, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group)
      (by
        rintro _ ⟨y, hy, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show (g⁻¹ * y * g⁻¹⁻¹) ^ 2 = g⁻¹ * y ^ 2 * g by rw [sq, sq]; group,
          hσ.sq_eq_one_of_mem_X hy, mul_one, inv_mul_cancel])
    exact hE ⟨x, hx, by simp⟩
  have hgX : g ∈ normalizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) := by
    have := mem_normalizer_of_conj_le hXg
    simpa using inv_mem this
  have hTg : ∀ y ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w,
      g⁻¹ * y * g⁻¹⁻¹ ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
    intro y hy
    rw [inv_inv, ← hCX]
    refine ⟨hRS'' ((hgR' y).mp (hTR₁ hy)), mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hx' : g * x * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} :=
      (mem_normalizer_iff.mp hgX x).mp hx
    have hc := (mem_centralizer_iff.mp (hσ.X_le_center_T hx').2 y hy)
    calc x * (g⁻¹ * y * g) = g⁻¹ * ((g * x * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * x * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * y * g * x := by group
  have hgT : g ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) := by
    have := mem_normalizer_of_conj_le hTg
    simpa using inv_mem this
  exact ⟨g, hgF, hgT, hgt⟩

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
