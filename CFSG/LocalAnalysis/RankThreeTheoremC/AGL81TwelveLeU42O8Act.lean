module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.Quasithin.Vol2.Ch10SecDFrattini
import CFSG.LocalAnalysis.SectionRank.CentralLift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.U42O8

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup

theorem conj_injective_of_center_eq_bot {Y : Type} [Group Y] (hcen : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have hzc : z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 := congrArg (fun σ : MulAut Y => σ x) hz
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc x * z = (z * x * z⁻¹) * z := by rw [h1]
      _ = z * x := by group
  rwa [hcen, Subgroup.mem_bot] at hzc

theorem exists_mem_of_normalizer_of_inner {A : Type} [Group A] [Finite A] {Y P : Subgroup A}
    (hcen : Subgroup.center ↥Y = ⊥)
    (hinner : ∀ α : MulAut ↥Y, Odd (orderOf α) → ∃ g : ↥Y, α = MulAut.conj g)
    (hP : IsParabolicTwo Y P) {b : A} (hb : Odd (orderOf b))
    (hbY : b ∈ normalizer (Y : Set A)) (hbP : b ∈ normalizer (P : Set A)) :
    ∃ y ∈ P, Odd (orderOf y) ∧ ∀ w ∈ Y, b * w * b⁻¹ = y * w * y⁻¹ := by
  classical
  obtain ⟨hPY, T, hT, hTN⟩ := hP
  let α : MulAut ↥Y := Y.normalizerMonoidHom ⟨b, hbY⟩
  have hαcoe : ∀ y : ↥Y, (α y : A) = b * (y : A) * b⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Y ⟨b, hbY⟩ y
  have hαodd : Odd (orderOf α) := by
    refine hb.of_dvd_nat ?_
    have h := orderOf_map_dvd Y.normalizerMonoidHom (⟨b, hbY⟩ : ↥(normalizer (Y : Set A)))
    rwa [Subgroup.orderOf_mk] at h
  obtain ⟨g, hg⟩ := hinner α hαodd
  have hker : ∀ z : ↥Y, MulAut.conj z = 1 → z = 1 := fun z hz =>
    conj_injective_of_center_eq_bot hcen (hz.trans (map_one MulAut.conj).symm)
  have hgodd : Odd (orderOf g) := by
    have h1 : MulAut.conj (g ^ orderOf α) = 1 := by
      rw [map_pow, ← hg, pow_orderOf_eq_one]
    exact hαodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one (hker _ h1))
  let y : A := (g : A)
  have hyodd : Odd (orderOf y) := by
    rw [Subgroup.orderOf_coe g]
    exact hgodd
  have hconj : ∀ w ∈ Y, b * w * b⁻¹ = y * w * y⁻¹ := by
    intro w hw
    have h1 : α ⟨w, hw⟩ = MulAut.conj g ⟨w, hw⟩ := by rw [hg]
    have h2 : ((α ⟨w, hw⟩ : ↥Y) : A) = b * w * b⁻¹ := hαcoe ⟨w, hw⟩
    rw [← h2, h1, MulAut.conj_apply]
    rfl
  have hyY : y ∈ Y := g.2
  have hyN : y ∈ normalizer (P : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have h := hconj w (hPY hw)
      rw [← h]
      exact (Subgroup.mem_normalizer_iff.mp hbP w).mp hw
    · intro hw
      have hwY : w ∈ Y := by
        have h1 : y⁻¹ * (y * w * y⁻¹) * y ∈ Y :=
          Y.mul_mem (Y.mul_mem (Y.inv_mem hyY) (hPY hw)) hyY
        simpa [mul_assoc] using h1
      have h := hconj w hwY
      exact (Subgroup.mem_normalizer_iff.mp hbP w).mpr (by rwa [← h] at hw)
  have hTP : T ≤ P := fun t ht => hTN ⟨hT.1 ht, le_normalizer ht⟩
  have hTP' : IsSylowTwoOf T P := by
    refine ⟨hTP, hT.2.1, ?_⟩
    intro h2
    have e : (T.subgroupOf P).index * (P.subgroupOf Y).index = (T.subgroupOf Y).index :=
      Subgroup.relIndex_mul_relIndex T P Y hTP hPY
    exact hT.2.2 (e ▸ dvd_mul_of_dvd_left h2 _)
  obtain ⟨n, hnP, hnyN⟩ :=
    CFSG.Quasithin.Vol2.Ch10.SecD.exists_mul_mem_normalizer hTP' hyN
  have hnyY : n * y ∈ Y := Y.mul_mem (hPY hnP) hyY
  have hyP : y ∈ P := by
    have h : n * y ∈ P := hTN ⟨hnyY, hnyN⟩
    have h' : n⁻¹ * (n * y) ∈ P := P.mul_mem (P.inv_mem hnP) h
    simpa using h'
  exact ⟨y, hyP, hyodd, hconj⟩

theorem exists_centralizing_of_card_le_nine {A : Type} [Group A] [Finite A] {Y P E : Subgroup A}
    (hcen : Subgroup.center ↥Y = ⊥)
    (hinner : ∀ α : MulAut ↥Y, Odd (orderOf α) → ∃ g : ↥Y, α = MulAut.conj g)
    (hP : IsParabolicTwo Y P) (h9 : ∀ T : Subgroup A, T ≤ P → IsPGroup 3 T → Nat.card T ≤ 9)
    (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEY : E ≤ normalizer (Y : Set A)) (hEP : E ≤ normalizer (P : Set A)) :
    ∃ c ∈ E, c ≠ 1 ∧ ∀ w ∈ Y, c * w = w * c := by
  classical
  have hPY : P ≤ Y := hP.1
  have hinj := conj_injective_of_center_eq_bot hcen
  let ψ : ↥E →* MulAut ↥Y := Y.normalizerMonoidHom.comp (Subgroup.inclusion hEY)
  have hψ : ∀ (e : ↥E) (w : ↥Y), ((ψ e w : ↥Y) : A) = (e : A) * w * (e : A)⁻¹ := fun e w =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Y ⟨(e : A), hEY e.2⟩ w
  have hcube : ∀ e : ↥E, e ^ 3 = 1 := fun e => Subtype.ext (hE.2 e e.2)
  have hodd : ∀ e : ↥E, Odd (orderOf (e : A)) := fun e =>
    (show Odd 3 by decide).of_dvd_nat (orderOf_dvd_of_pow_eq_one (hE.2 e e.2))
  have hact : ∀ e : ↥E, ∃ g : ↥Y, ψ e = MulAut.conj g ∧ (g : A) ∈ P := by
    intro e
    obtain ⟨y, hyP, -, hy⟩ := exists_mem_of_normalizer_of_inner hcen hinner hP (hodd e)
      (hEY e.2) (hEP e.2)
    refine ⟨⟨y, hPY hyP⟩, ?_, hyP⟩
    ext w
    rw [hψ, MulAut.conj_apply]
    exact hy w w.2
  set R' : Subgroup ↥Y := ψ.range.comap (MulAut.conj : ↥Y →* MulAut ↥Y) with hR'
  have hRle : ψ.range ≤ (MulAut.conj : ↥Y →* MulAut ↥Y).range := by
    rintro _ ⟨e, rfl⟩
    obtain ⟨g, hg, -⟩ := hact e
    exact ⟨g, hg.symm⟩
  have hcardR' : Nat.card R' = Nat.card ψ.range := by
    have h1 : R'.map (MulAut.conj : ↥Y →* MulAut ↥Y) = ψ.range := by
      rw [hR', Subgroup.map_comap_eq, inf_eq_right.2 hRle]
    rw [← h1]
    exact (Subgroup.card_map_of_injective hinj).symm
  have hR'P : ∀ g ∈ R', (g : A) ∈ P := by
    intro g hg
    obtain ⟨e, he⟩ := Subgroup.mem_comap.1 hg
    obtain ⟨g', hg', hg'P⟩ := hact e
    have : g = g' := hinj (he.symm.trans hg')
    rw [this]
    exact hg'P
  have hR'cube : ∀ g ∈ R', g ^ 3 = 1 := by
    intro g hg
    obtain ⟨e, he⟩ := Subgroup.mem_comap.1 hg
    apply hinj
    rw [map_pow, ← he, ← map_pow, hcube e, map_one, map_one]
  set T : Subgroup A := R'.map Y.subtype with hT
  have hTP : T ≤ P := by
    rintro _ ⟨g, hg, rfl⟩
    exact hR'P g hg
  have hTp : IsPGroup 3 ↥T := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
    refine ⟨1, Subtype.ext ?_⟩
    simpa using congrArg Subtype.val (hR'cube g hg)
  have hT9 : Nat.card ψ.range ≤ 9 := by
    have h1 : Nat.card T = Nat.card R' := Subgroup.card_map_of_injective Y.subtype_injective
    rw [← hcardR', ← h1]
    exact h9 T hTP hTp
  have hmul := Subgroup.card_ker_mul_card_range ψ
  rw [hE27] at hmul
  have hker3 : 3 ≤ Nat.card ψ.ker := by
    by_contra hlt
    have hkr : Nat.card ψ.ker * Nat.card ψ.range ≤ 2 * 9 :=
      Nat.mul_le_mul (by omega) hT9
    omega
  have hne : ψ.ker ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hker3
    omega
  obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  refine ⟨((c : ↥E) : A), c.1.2, fun h => hc1 ?_, fun w hw => ?_⟩
  · exact Subtype.ext (Subtype.ext h)
  · have h1 := hψ c.1 ⟨w, hw⟩
    rw [MonoidHom.mem_ker.1 c.2, MulAut.one_apply] at h1
    have h2 : (w : A) = (c.1 : A) * w * (c.1 : A)⁻¹ := h1
    calc (c.1 : A) * w = ((c.1 : A) * w * (c.1 : A)⁻¹) * (c.1 : A) := by group
      _ = w * c.1 := by rw [← h2]

theorem false_of_card_le_nine {A : Type} [Group A] [Finite A] {Y P E F : Subgroup A}
    (hcen : Subgroup.center ↥Y = ⊥)
    (hinner : ∀ α : MulAut ↥Y, Odd (orderOf α) → ∃ g : ↥Y, α = MulAut.conj g)
    (hP : IsParabolicTwo Y P) (h9 : ∀ T : Subgroup A, T ≤ P → IsPGroup 3 T → Nat.card T ≤ 9)
    (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEY : E ≤ normalizer (Y : Set A)) (hEP : E ≤ normalizer (P : Set A))
    (hFY : F ≤ Y) (hF : IsElemAbelian 3 F) (hF27 : Nat.card F = 27)
    (hrk : Open.pRank 3 (Y ⊔ E) ≤ 3) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hcE, hc1, hcY⟩ :=
    exists_centralizing_of_card_le_nine hcen hinner hP h9 hE hE27 hEY hEP
  have hc3 : c ^ 3 = 1 := hE.2 c hcE
  have hcnY : c ∉ Y := by
    intro hcY'
    have hc : (⟨c, hcY'⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (hcY w w.2).symm
    rw [hcen, Subgroup.mem_bot] at hc
    exact hc1 (congrArg Subtype.val hc)
  have hc1' : c ∉ (F.subtype : ↥F →* A).range := by
    rintro ⟨f, hf⟩
    exact hcnY (hf ▸ hFY f.2)
  obtain ⟨F', hF'inj, hF'comm, hF'pow, hF'card, hF'rep⟩ :=
    CFSG.SectionRank.exists_extend (p := 3) (B := ↥F) (fun a b => hF.1.is_comm.comm a b)
      (fun a => Subtype.ext (hF.2 a a.2)) (k := 3) (by rw [hF27]; norm_num) F.subtype
      Subtype.val_injective (y := c) hc3 hc1' (fun b => (hcY (b : A) (hFY b.2)).symm)
  have hel : IsElemAbelian 3 F'.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun g hg => ?_⟩
    · obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      change (a : A) * b = b * a
      rw [← hu, ← hv, ← map_mul, ← map_mul, hF'comm u v]
    · obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hg
      rw [← map_pow, hF'pow u, map_one]
  have hcard : Nat.card F'.range = 3 ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hF'inj).toEquiv, hF'card]
  have hle : F'.range ≤ Y ⊔ E := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, n, hb⟩ := hF'rep a
    rw [hb]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hFY b.2))
      (Subgroup.mem_sup_right (E.pow_mem hcE n))
  have h4 := CFSG.SectionRank.le_pRank (by norm_num) hle hel hcard
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.U42O8
