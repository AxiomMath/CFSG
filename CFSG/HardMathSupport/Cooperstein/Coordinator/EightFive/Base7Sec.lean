module

public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Background.B1MoreQuot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin

variable {V : Type*} [CommGroup V] {K : Subgroup (MulAut V)} {Y₀ Y₁ : Subgroup V}

@[expose] noncomputable def secHom (h₀ : K ≤ stabSub Y₀) (h₁ : K ≤ stabSub Y₁) :
    ↥K →* MulAut (Sec Y₁ Y₀) :=
  (quotHom (Y₀.subgroupOf Y₁)).comp
    (((resHom Y₁).comp (Subgroup.inclusion h₁)).codRestrict (stabSub (Y₀.subgroupOf Y₁))
      fun k y => by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact h₀ k.2 y)

theorem secHom_mk (h₀ : K ≤ stabSub Y₀) (h₁ : K ≤ stabSub Y₁) (k : ↥K) (y : ↥Y₁) :
    secHom h₀ h₁ k (QuotientGroup.mk y) =
      QuotientGroup.mk ⟨(k : MulAut V) y, (h₁ k.2 y).2 y.2⟩ :=
  rfl

theorem mk_eq_mk_sec_iff (a b : ↥Y₁) :
    (QuotientGroup.mk a : Sec Y₁ Y₀) = QuotientGroup.mk b ↔ (a : V) * (b : V)⁻¹ ∈ Y₀ := by
  rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv, Subgroup.mem_subgroupOf]
  rfl

theorem mk_eq_one_sec_iff (a : ↥Y₁) : (QuotientGroup.mk a : Sec Y₁ Y₀) = 1 ↔ (a : V) ∈ Y₀ := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem range_secHom (h₀ : K ≤ stabSub Y₀) (h₁ : K ≤ stabSub Y₁) :
    (secHom h₀ h₁).range = autSec K Y₁ Y₀ := by
  ext φ
  constructor
  · rintro ⟨k, rfl⟩
    exact mem_autQuot.2 ⟨_, mem_autSub.2 ⟨⟨k, h₁ k.2⟩, k.2, rfl⟩, rfl⟩
  · intro hφ
    obtain ⟨g, hg, rfl⟩ := mem_autQuot.1 hφ
    obtain ⟨k, hk, hkg⟩ := mem_autSub.1 hg
    refine ⟨⟨k, hk⟩, ?_⟩
    change quotHom _ _ = quotHom _ g
    congr 1
    exact Subtype.ext hkg

theorem map_secHom (h₀ : K ≤ stabSub Y₀) (h₁ : K ≤ stabSub Y₁) {B : Subgroup (MulAut V)}
    (hBK : B ≤ K) : (B.subgroupOf K).map (secHom h₀ h₁) = autSec B Y₁ Y₀ := by
  rw [← range_secHom (hBK.trans h₀) (hBK.trans h₁)]
  ext φ
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨⟨b, hBK b.2⟩, b.2, rfl⟩

theorem secHom_eq_one_iff (h₀ : K ≤ stabSub Y₀) (h₁ : K ≤ stabSub Y₁) (k : ↥K) :
    secHom h₀ h₁ k = 1 ↔ ∀ y ∈ Y₁, (k : MulAut V) y * y⁻¹ ∈ Y₀ := by
  constructor
  · intro h y hy
    have h1 := congrArg (fun φ : MulAut (Sec Y₁ Y₀) => φ (QuotientGroup.mk ⟨y, hy⟩)) h
    simp only [secHom_mk, MulAut.one_apply] at h1
    exact (mk_eq_mk_sec_iff _ _).1 h1
  · intro h
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H y => exact (mk_eq_mk_sec_iff _ _).2 (h y y.2)

theorem secHom_injective (h₀ : K ≤ stabSub Y₀) (h₁ : K ≤ stabSub Y₁)
    (hK : K ⊓ centSec Y₁ Y₀ = ⊥) : Function.Injective (secHom h₀ h₁) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hmem : (k : MulAut V) ∈ K ⊓ centSec Y₁ Y₀ :=
    ⟨k.2, h₁ k.2, (secHom_eq_one_iff h₀ h₁ k).1 hk⟩
  rw [hK] at hmem
  exact Subtype.ext (Subgroup.mem_bot.1 hmem)

theorem mk_mem_fixV_autSec_iff {B : Subgroup (MulAut V)} (hB₀ : B ≤ stabSub Y₀)
    (hB₁ : B ≤ stabSub Y₁) (y : ↥Y₁) :
    (QuotientGroup.mk y : Sec Y₁ Y₀) ∈ fixV (autSec B Y₁ Y₀) ↔
      ∀ b ∈ B, b (y : V) * (y : V)⁻¹ ∈ Y₀ := by
  rw [← range_secHom hB₀ hB₁]
  constructor
  · intro h b hb
    have h1 := h _ ⟨⟨b, hb⟩, rfl⟩
    rw [secHom_mk] at h1
    exact (mk_eq_mk_sec_iff _ _).1 h1
  · rintro h _ ⟨b, rfl⟩
    rw [secHom_mk]
    exact (mk_eq_mk_sec_iff _ _).2 (h b b.2)

theorem isIrrSec_autSec {L : Subgroup (MulAut V)} (h₀ : L ≤ stabSub Y₀) (h₁ : L ≤ stabSub Y₁)
    (hlt : Y₀ < Y₁)
    (hirr : ∀ Y : Subgroup V, (∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y) → Y₀ ≤ Y → Y ≤ Y₁ → Y = Y₀ ∨ Y = Y₁) :
    XMod.IsIrrSec ↥(autSec L Y₁ Y₀) (⊥ : Subgroup (Sec Y₁ Y₀)) ⊤ := by
  refine ⟨?_, fun J hJ _ _ => ?_⟩
  · obtain ⟨y, hy1, hy0⟩ := IsConcreteLE.exists_of_lt hlt
    refine bot_lt_iff_ne_bot.2 fun h => hy0 ?_
    have h1 : (QuotientGroup.mk ⟨y, hy1⟩ : Sec Y₁ Y₀) ∈ (⊥ : Subgroup (Sec Y₁ Y₀)) :=
      h ▸ Subgroup.mem_top _
    exact (mk_eq_one_sec_iff _).1 (Subgroup.mem_bot.1 h1)
  · set Y : Subgroup V := (J.comap (QuotientGroup.mk' (Y₀.subgroupOf Y₁))).map Y₁.subtype with hY
    have hmemY : ∀ y : ↥Y₁, (y : V) ∈ Y ↔ (QuotientGroup.mk y : Sec Y₁ Y₀) ∈ J := by
      intro y
      constructor
      · rintro ⟨z, hz, hzy⟩
        rw [← Subtype.ext hzy]
        exact hz
      · intro h
        exact ⟨y, h, rfl⟩
    have hYY₁ : Y ≤ Y₁ := Subgroup.map_subtype_le _
    have hinv : ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y := by
      rintro l hl _ ⟨z, hz, rfl⟩
      have hz' : (QuotientGroup.mk z : Sec Y₁ Y₀) ∈ J := hz
      have h1 := hJ ⟨secHom h₀ h₁ ⟨l, hl⟩, (range_secHom h₀ h₁) ▸ ⟨⟨l, hl⟩, rfl⟩⟩ _ hz'
      exact (hmemY ⟨l z, (h₁ hl z).2 z.2⟩).2 h1
    have hY₀Y : Y₀ ≤ Y := fun y hy => by
      have hy1 : y ∈ Y₁ := hlt.le hy
      refine (hmemY ⟨y, hy1⟩).2 ?_
      rw [(mk_eq_one_sec_iff _).2 hy]
      exact J.one_mem
    rcases hirr Y hinv hY₀Y hYY₁ with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      have h1 := (hmemY y).2 hx
      rw [h] at h1
      exact Subgroup.mem_bot.2 ((mk_eq_one_sec_iff _).2 h1)
    · right
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      exact (hmemY y).1 (by rw [h]; exact y.2)

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
