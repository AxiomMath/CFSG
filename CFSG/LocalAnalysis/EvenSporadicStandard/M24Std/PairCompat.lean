module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TCheck
public import Certificates.Certificate24853

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.QuasithinUnique.Setup.X1

variable {G : Type} [Group G]

namespace ListImage

variable {L A B Z : Subgroup G} {e : L ≃* NativeSporadic.M24}

theorem pinV_comm (e : L ≃* NativeSporadic.M24) (a x : S24) :
    pinV e a * (pinV e x * (pinV e a)⁻¹ * (pinV e x)⁻¹) = pinV e (a * (x * a⁻¹ * x⁻¹)) := by
  simp only [map_mul, map_inv]

theorem compat_comm_A (hA : ListImage L e A m24E1l)
    (hB : ListImage L e B m24B0l) :
    ∀ x ∈ B, x ∉ A →
      (∀ a ∈ A, a * (x * a⁻¹ * x⁻¹) ∈ B) ∧ ∀ b ∈ A ⊓ B, ∃ a ∈ A, b = a * (x * a⁻¹ * x⁻¹) := by
  obtain ⟨⟨-, -, -, hcommA⟩, -, -⟩ := Certificates.certificate24853
  intro x hx hxA
  obtain ⟨qx, hqx, rfl⟩ := hB.exists_eq hx
  have hqxA : qx ∉ m24E1l := fun h => hxA ((hA.pinV_mem_iff qx).2 h)
  obtain ⟨h1, h2⟩ := hcommA qx hqx hqxA
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨qa, hqa, rfl⟩ := hA.exists_eq ha
    rw [pinV_comm, hB.pinV_mem_iff]
    exact h1 qa hqa
  · obtain ⟨qb, hqb, rfl⟩ := (hA.inf hB).exists_eq hb
    rw [List.mem_filter, decide_eq_true_iff] at hqb
    obtain ⟨qa, hqa, hqe⟩ := h2 qb hqb.2 hqb.1
    exact ⟨pinV e qa, (hA.pinV_mem_iff qa).2 hqa, by rw [pinV_comm, hqe]⟩

theorem compat_Z_ex
    (hA : ListImage L e A m24E1l) (hB : ListImage L e B m24B0l)
    (hZ : ListImage L e Z pairZl) :
    Z ≤ A ∧ EgElemAb Z ∧ Nat.card Z = 16 ∧ Z ⊓ B = ⊥ ∧
      Subgroup.closure {x : G | x ∈ Z ∧ (∀ b ∈ B, b * (x * b⁻¹ * x⁻¹) ∈ A ⊓ B) ∧
        ∀ c ∈ A ⊓ B, ∃ b ∈ B, c = b * (x * b⁻¹ * x⁻¹)} = Z ∧
      ∃ y ∈ egNL L B, y ∈ normalizer (Z : Set G) ∧ y * y * y = 1 ∧
        (∀ b ∈ B, y * b * y⁻¹ = b ↔ b ∈ A) ∧
        Subgroup.closure {w : G | ∃ x ∈ Z, w = x * (y * x⁻¹ * y⁻¹)} = Z := by
  obtain ⟨-, -, -, -, hE1sq, hE1comm, -⟩ := m24_e1_check
  obtain ⟨-, ⟨hZlen, hZnd, -, -, hZA, hZB, hZbas, hZgen⟩,
    ⟨hyB, hyZ, hy3, hyfix, hyc, hygen⟩⟩ := Certificates.certificate24853
  have hZl : ∀ q ∈ pairZl, ∃ n, q = m24Elt4 pairZB n := by
    intro q hq
    obtain ⟨n, -, rfl⟩ := List.mem_map.1 hq
    exact ⟨n, rfl⟩
  have hAB := hA.inf hB
  refine ⟨?_, ?_, (hZ.card hZnd).trans hZlen, ?_, ?_, pinV e pairY, hB.pinV_mem_egNL hyB,
    hZ.pinV_mem_normalizer hyZ, by rw [← map_mul, ← map_mul, hy3, map_one], ?_, ?_⟩
  · intro g hg
    obtain ⟨q, hq, rfl⟩ := hZ.exists_eq hg
    exact (hA.pinV_mem_iff q).2 (hZA q hq)
  · exact hZ.elemAb (fun a ha b hb => hE1comm a (hZA a ha) b (hZA b hb))
      (fun a ha => hE1sq a (hZA a ha))
  · rw [eq_bot_iff_forall]
    intro g hg
    obtain ⟨q, hq, rfl⟩ := hZ.exists_eq (mem_inf.1 hg).1
    rw [hZB q hq ((hB.pinV_mem_iff q).1 (mem_inf.1 hg).2), map_one]
  · refine hZ.closure_eq (fun x hx => hx.1) hZl fun z hz => ⟨(hZ.pinV_mem_iff z).2 (hZbas z hz),
      fun b hb => ?_, fun c hc => ?_⟩
    · obtain ⟨qb, hqb, rfl⟩ := hB.exists_eq hb
      obtain ⟨h1, h2⟩ := (hZgen z hz).1 qb hqb
      rw [pinV_comm]
      exact mem_inf.2 ⟨(hA.pinV_mem_iff _).2 h1, (hB.pinV_mem_iff _).2 h2⟩
    · obtain ⟨qc, hqc, rfl⟩ := hAB.exists_eq hc
      rw [List.mem_filter, decide_eq_true_iff] at hqc
      obtain ⟨qb, hqb, hqe⟩ := (hZgen z hz).2 qc hqc.2 hqc.1
      exact ⟨pinV e qb, (hB.pinV_mem_iff qb).2 hqb, by rw [pinV_comm, hqe]⟩
  · intro b hb
    obtain ⟨qb, hqb, rfl⟩ := hB.exists_eq hb
    rw [hA.pinV_mem_iff, ← hyfix qb hqb, ← map_inv, ← map_mul, ← map_mul]
    exact (pinV_injective e).eq_iff
  · refine hZ.closure_eq ?_ hZl fun z hz => ?_
    · rintro w ⟨x, hx, rfl⟩
      obtain ⟨q, hq, rfl⟩ := hZ.exists_eq hx
      rw [pinV_comm, SetLike.mem_coe, hZ.pinV_mem_iff]
      exact hyc q hq
    · obtain ⟨x, hx, hxe⟩ := hygen z hz
      exact ⟨pinV e x, (hZ.pinV_mem_iff x).2 hx, by rw [pinV_comm, hxe]⟩

theorem compatFacts
    (hA : ListImage L e A m24E1l) (hB : ListImage L e B m24B0l) : CompatFacts L A B := by
  obtain ⟨hE1len, hE1nd, -⟩ := m24_e1_check
  obtain ⟨⟨hAB, hBA, hcard, -⟩, ⟨-, -, hZ1, hZmul, -⟩, -⟩ := Certificates.certificate24853
  obtain ⟨Z, hZ⟩ := exists_listImage e hZ1 hZmul
  refine ⟨fun g hg => ?_, fun g hg => ?_, ?_, hA.compat_comm_A hB, ⟨Z, hA.compat_Z_ex hB hZ⟩⟩
  · obtain ⟨q, hq, rfl⟩ := hB.exists_eq hg
    exact hA.pinV_mem_egNL (hBA q hq)
  · obtain ⟨q, hq, rfl⟩ := hA.exists_eq hg
    exact hB.pinV_mem_egNL (hAB q hq)
  · rw [(hA.inf hB).card (hE1nd.filter _)]
    exact hcard

end ListImage

theorem compatFacts_of_pair
    {L A B : Subgroup G} (h : PairType L A B) : CompatFacts L A B := by
  obtain ⟨e, hA, hB⟩ := h.exists_listImage
  exact hA.compatFacts hB

end CFSG.EvenSporadicStandard.M24Std
