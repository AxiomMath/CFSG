module

public import CFSG.CGT.PushingUpLit.BHS5.FiveSixLift

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.LieType.BorelTits
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5

section Aut

variable {V : Type} [CommGroup V] [Finite V]

theorem quotHom_injective_of_pCoreOf_eq_bot (hV : ∀ v : V, v ^ 2 = 1) {K : Subgroup (MulAut V)}
    (ho2 : pCoreOf 2 K = ⊥) : Function.Injective (BHS5.quotHom K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  set C : Subgroup (MulAut V) := (BHS5.quotHom K).ker.map K.subtype with hC
  have hCK : C ≤ K := Subgroup.map_subtype_le _
  have hCsub : C.subgroupOf K = (BHS5.quotHom K).ker :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hCn : K ≤ Subgroup.normalizer (C : Set (MulAut V)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCK).1 (hCsub ▸ MonoidHom.normal_ker _)
  have hkey : ∀ c ∈ C, ∀ v : V, c v * v⁻¹ ∈ fixOp K := by
    rintro _ ⟨c', hc', rfl⟩ v
    exact (BHS5.mem_ker_quotHom K c').1 hc' v
  have hodd : ∀ x ∈ C, Odd (orderOf x) → x = 1 := by
    intro x hxC hxo
    have hxO : x ∈ opResidual 2 K :=
      mem_opResidual_of_coprime (hCK hxC) (Nat.coprime_two_right.2 hxo)
    refine MulEquiv.ext fun v => ?_
    exact apply_eq_of_quad_odd hV hxo (hkey x hxC v x hxO)
  have hres : opResidual 2 C ≤ ⊥ := by
    rw [opResidual, Subgroup.closure_le]
    rintro x ⟨hxC, hxc⟩
    exact (Subgroup.mem_bot).2 (hodd x hxC (Nat.coprime_two_right.1 hxc))
  have hC2 : IsPGroup 2 ↥C := by
    intro c
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := exists_pow_mem_opResidual (p := 2) (A := C) c.2
    refine ⟨k, Subtype.ext ?_⟩
    have := hres hk
    simpa using this
  have hCbot : C ≤ ⊥ := ho2 ▸ le_pCoreOf_of_le_normalizer 2 hCK hCn hC2
  have h1 := hCbot (show (g : MulAut V) ∈ C from ⟨g, hg, rfl⟩)
  rw [Subgroup.mem_bot] at h1
  exact Subtype.ext h1

@[expose] noncomputable def qImg (K X : Subgroup (MulAut V)) :
    Subgroup (MulAut (V ⧸ fixOp K)) :=
  (X.subgroupOf K).map (BHS5.quotHom K)

omit [Finite V] in
theorem mem_qImg {K X : Subgroup (MulAut V)} {y : MulAut (V ⧸ fixOp K)} :
    y ∈ qImg K X ↔ ∃ x : ↥K, (x : MulAut V) ∈ X ∧ BHS5.quotHom K x = y := by
  unfold qImg
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h⟩⟩

omit [Finite V] in
theorem qImg_mono {K X Y : Subgroup (MulAut V)} (h : X ≤ Y) : qImg K X ≤ qImg K Y :=
  Subgroup.map_mono (Subgroup.comap_mono h)

omit [Finite V] in
theorem qImg_le_range {K X : Subgroup (MulAut V)} :
    qImg K X ≤ (⊤ : Subgroup ↥K).map (BHS5.quotHom K) :=
  Subgroup.map_mono le_top

omit [Finite V] in
theorem card_qImg {K X : Subgroup (MulAut V)} (hinj : Function.Injective (BHS5.quotHom K))
    (hXK : X ≤ K) : Nat.card (qImg K X) = Nat.card X := by
  rw [qImg, Subgroup.card_map_of_injective hinj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv

omit [Finite V] in
theorem quotHom_apply_mk_eq_iff {K : Subgroup (MulAut V)} (x : ↥K) (v : V) :
    BHS5.quotHom K x (QuotientGroup.mk v : V ⧸ fixOp K) = QuotientGroup.mk v ↔
      (x : MulAut V) v * v⁻¹ ∈ fixOp K := by
  rw [BHS5.quotHom_mk, QuotientGroup.eq, ← inv_mem_iff (x := (x : MulAut V) v * v⁻¹)]
  simp [mul_comm]

variable {K : Subgroup (MulAut V)}

theorem exists_isOffStar_quot (hinj : Function.Injective (BHS5.quotHom K))
    {A : Subgroup (MulAut V)} (hAK : A ≤ K) (hA : IsOffStar A) :
    ∃ B : Subgroup (MulAut V), B ≤ A ∧ IsOffStar (qImg K B) := by
  set Ã : Subgroup (MulAut (V ⧸ fixOp K)) := qImg K A with hÃ
  have hcardÃ : Nat.card Ã = Nat.card A := card_qImg hinj hAK
  have hZpos : 0 < Nat.card (fixOp K) := Nat.card_pos
  have hVcard : Nat.card V = Nat.card (V ⧸ fixOp K) * Nat.card (fixOp K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (fixOp K)
  have hwÃ : Nat.card (V ⧸ fixOp K) < Nat.card Ã * Nat.card (fixV Ã) := by
    have h1 : Nat.card V < Nat.card A * Nat.card (fixV A) := hA.2
    have h2 := card_fixV_le_quot (P := K) (B := A)
    refine lt_of_mul_lt_mul_right ?_ (Nat.zero_le (Nat.card (fixOp K)))
    calc Nat.card (V ⧸ fixOp K) * Nat.card (fixOp K) = Nat.card V := hVcard.symm
      _ < Nat.card A * Nat.card (fixV A) := h1
      _ ≤ Nat.card A * (Nat.card (fixV Ã) * Nat.card (fixOp K)) := Nat.mul_le_mul_left _ h2
      _ = Nat.card Ã * Nat.card (fixV Ã) * Nat.card (fixOp K) := by rw [hcardÃ]; ring
  obtain ⟨B₀, hB₀, hmax⟩ := Set.exists_max_image
    {B : Subgroup (MulAut (V ⧸ fixOp K)) | B ≤ Ã}
    (fun B => Nat.card B * Nat.card (fixV B)) (Set.toFinite _) ⟨⊥, (bot_le : ⊥ ≤ Ã)⟩
  have hwB₀ : Nat.card (V ⧸ fixOp K) < Nat.card B₀ * Nat.card (fixV B₀) :=
    hwÃ.trans_le (hmax Ã (le_rfl : Ã ≤ Ã))
  have hB₀ne : B₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, B1.card_bot_mul_card_fixV] at hwB₀
    exact lt_irrefl _ hwB₀
  have hoff : IsOff B₀ :=
    ⟨le_top, hB₀ne, isElemAbelian2_mono' (isElemAbelian2_map_quot hA.1.2.2.1) hB₀,
      fun C hC => hmax C (hC.trans hB₀)⟩
  have hB₀le : B₀ ≤ (⊤ : Subgroup ↥K).map (BHS5.quotHom K) := hB₀.trans qImg_le_range
  refine ⟨liftQ K B₀, ?_, ?_⟩
  · have := liftQ_mono hB₀
    rwa [hÃ, qImg, liftQ_quotImg hinj hAK] at this
  · have h := quotImg_liftQ hB₀le
    show IsOffStar (((liftQ K B₀).subgroupOf K).map (BHS5.quotHom K))
    rw [h]
    exact ⟨hoff, hwB₀⟩

end Aut

end CFSG.CGT.PushingUpLit.BHS7
