module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ThirteenCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ThirteenSteps

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

variable {G : Type} [Group G]

namespace Thirteen

theorem ndata_mem_of_comm_z [Finite G] {B D : Subgroup G} {z : G} (hD : NData B z D)
    (hBz : ∀ b ∈ B, b * z = z * b) (hB : 16 ≤ Nat.card B) :
    ∀ d ∈ D, z * d * z⁻¹ * d⁻¹ = 1 → d ∈ B := by
  have hsub := subset_of_card_le (S := (D : Set G)) (T := (B : Set G))
    (U := {d | d ∈ D ∧ z * d * z⁻¹ * d⁻¹ = 1}) (fun g => z * g * z⁻¹ * g⁻¹) hD.onto
    (fun s hs u hu => ⟨D.mul_mem hs hu.1, comm_z_mul_of_eq_one hu.2⟩)
    (fun b hb => ⟨hD.B_le hb, comm_z_eq_one_of_comm (hBz b hb)⟩)
    (by
      show Nat.card D ≤ Nat.card B * Nat.card B
      rw [hD.card]
      nlinarith)
    (by
      show 0 < Nat.card B
      omega)
  exact fun d hd h1 => hsub ⟨hd, h1⟩

theorem cdata_mem_of_comm_z [Finite G] {A C : Subgroup G} {z : G} (hC : CData A z C)
    (hAz : ∀ a ∈ A, a * z = z * a) (hA : 64 ≤ Nat.card A) :
    (∀ c ∈ C, z * c * z⁻¹ * c⁻¹ = 1 → c ∈ A) ∧ Nat.card A ≤ 64 := by
  obtain ⟨U, hU⟩ : ∃ U : Set G, U = {c | c ∈ C ∧ z * c * z⁻¹ * c⁻¹ = 1} := ⟨_, rfl⟩
  have hT' : ∀ a ∈ (A : Set G), ∃ c ∈ (C : Set G), (fun g => z * g * z⁻¹ * g⁻¹) c = a := hC.onto
  have hU' : ∀ s ∈ (C : Set G), ∀ u ∈ U, s * u ∈ (C : Set G) ∧
      (fun g => z * g * z⁻¹ * g⁻¹) (s * u) = (fun g => z * g * z⁻¹ * g⁻¹) s := by
    rw [hU]
    exact fun s hs u hu => ⟨C.mul_mem hs hu.1, comm_z_mul_of_eq_one hu.2⟩
  have hAU : (A : Set G) ⊆ U := by
    rw [hU]
    exact fun a ha => ⟨hC.A_le ha, comm_z_eq_one_of_comm (hAz a ha)⟩
  have h1 : Nat.card A * Nat.card U ≤ Nat.card C := card_mul_card_le_of_const _ hT' hU'
  have h2 : Nat.card A ≤ Nat.card U := Set.ncard_le_ncard hAU
  refine ⟨fun c hc h => ?_, ?_⟩
  · have hsub := subset_of_card_le _ hT' hU' hAU (by
      show Nat.card C ≤ Nat.card A * Nat.card A
      rw [hC.card]
      nlinarith) (by
      show 0 < Nat.card A
      omega)
    exact hsub (by rw [hU]; exact ⟨hc, h⟩)
  · have h3 : Nat.card A * Nat.card A ≤ 64 * 64 :=
      calc Nat.card A * Nat.card A ≤ Nat.card A * Nat.card U := Nat.mul_le_mul_left _ h2
        _ ≤ Nat.card C := h1
        _ = 64 * 64 := hC.card.trans (by norm_num)
    exact Nat.mul_self_le_mul_self_iff.mp h3

theorem inj_of_inf_eq_bot {Z B B₁ : Subgroup G} (hZB : Z ⊓ B = ⊥) (hB₁ : B₁ ≤ B) :
    ∀ h ∈ (Z : Set G), ∀ h' ∈ (Z : Set G), ∀ k ∈ (B₁ : Set G), ∀ k' ∈ (B₁ : Set G),
      h * k = h' * k' → h = h' := by
  intro h hh h' hh' k hk k' hk' e
  have hm : h'⁻¹ * h ∈ Z ⊓ B := by
    refine mem_inf.mpr ⟨Z.mul_mem (Z.inv_mem hh') hh, ?_⟩
    have e' : h'⁻¹ * h = k' * k⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
    rw [e']
    exact B.mul_mem (hB₁ hk') (B.inv_mem (hB₁ hk))
  rw [hZB, mem_bot] at hm
  exact (inv_mul_eq_one.mp hm).symm

end Thirteen

open Thirteen

theorem cData_elem [Finite G] {L A B C D : Subgroup G} {z : G} (hs : LocalSetting G L z)
    (hF : CompatFacts L A B) (_hT : TranslationData A z) (hC : CData A z C)
    (hD : NData B z D) :
    ∀ c ∈ C, c * c = 1 := by
  rcases hC.dichotomy with h | hinv
  · exact h
  exfalso
  obtain ⟨Z, hZA, hZel, hZcard, hZB, hX, y, hyNL, -, hy3, hyB, hyZ⟩ := hF.Z_ex
  have hzL : ∀ g ∈ L, g * z = z * g := mem_centralizer_iff.mp (hs.z_central (mem_zpowers z))
  have hAL : ∀ a ∈ A, a ∈ L := fun a ha => (mem_inf.mp (hF.A_le_NB ha)).2
  have hBL : ∀ b ∈ B, b ∈ L := fun b hb => (mem_inf.mp (hF.B_le_NA hb)).2
  have hyz : y * z = z * y := hzL y (mem_inf.mp hyNL).2
  have hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a :=
    fun a ha a' ha' => hC.comm a (hC.A_le ha) a' (hC.A_le ha')
  obtain ⟨hDc, hD2⟩ := hD.elem
  have hBD : B ≤ D := hD.B_le
  have hzD : ∀ d ∈ D, z * d * z⁻¹ * d⁻¹ ∈ D := fun d hd => hBD (hD.comm_z d hd)
  have h4 : Nat.card (A ⊓ B : Subgroup G) = 4 := hF.card_inf
  obtain ⟨x₀, hx₀Z, -, hx₀2⟩ := nonempty_of_closure_eq hX (by rw [hZcard]; norm_num)
  have hB16 : 16 ≤ Nat.card B := by
    have h : Nat.card (A ⊓ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) ≤ Nat.card B :=
      card_mul_card_le_of_const (S := (B : Set G)) (T := ((A ⊓ B : Subgroup G) : Set G))
        (U := ((A ⊓ B : Subgroup G) : Set G)) (fun g => g * (x₀ * g⁻¹ * x₀⁻¹))
        (fun c hc => (hx₀2 c hc).imp fun b hb => ⟨hb.1, hb.2.symm⟩)
        (fun s hs u hu => ⟨B.mul_mem hs (mem_inf.mp hu).2, by
          have hux := hAc u (mem_inf.mp hu).1 x₀ (hZA hx₀Z)
          show s * u * (x₀ * (s * u)⁻¹ * x₀⁻¹) = s * (x₀ * s⁻¹ * x₀⁻¹)
          calc s * u * (x₀ * (s * u)⁻¹ * x₀⁻¹) = s * (u * x₀) * u⁻¹ * s⁻¹ * x₀⁻¹ := by group
            _ = s * (x₀ * u) * u⁻¹ * s⁻¹ * x₀⁻¹ := by rw [hux]
            _ = s * (x₀ * s⁻¹ * x₀⁻¹) := by group⟩)
    rw [h4] at h
    omega
  have hker : ∀ d ∈ D, z * d * z⁻¹ * d⁻¹ = 1 → d ∈ B :=
    ndata_mem_of_comm_z hD (fun b hb => hzL b (hBL b hb)) hB16
  have hA64 : 64 ≤ Nat.card A := by
    have h : Nat.card Z * Nat.card (A ⊓ B : Subgroup G) ≤ Nat.card A :=
      card_mul_card_le_of_inj (H := (Z : Set G)) (K := ((A ⊓ B : Subgroup G) : Set G))
        (S := (A : Set G)) (fun h hh k hk => A.mul_mem (hZA hh) (mem_inf.mp hk).1)
        (inj_of_inf_eq_bot hZB inf_le_right)
    rw [hZcard, h4] at h
    omega
  obtain ⟨hkerC, hA64'⟩ := cdata_mem_of_comm_z hC (fun a ha => hzL a (hAL a ha)) hA64
  have hAdec : ∀ a ∈ A, ∃ x ∈ Z, ∃ b ∈ A ⊓ B, a = x * b :=
    exists_mul_eq_of_card_le (H := (Z : Set G)) (K := ((A ⊓ B : Subgroup G) : Set G))
      (S := (A : Set G)) (fun h hh k hk => A.mul_mem (hZA hh) (mem_inf.mp hk).1)
      (inj_of_inf_eq_bot hZB inf_le_right) (by
        show Nat.card A ≤ Nat.card Z * Nat.card (A ⊓ B : Subgroup G)
        rw [hZcard, h4]
        omega)
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, K = D ⊓ centralizer {y} := ⟨_, rfl⟩
  have hmemK : ∀ k, k ∈ K ↔ k ∈ D ∧ y * k * y⁻¹ = k := by
    intro k
    rw [hK, mem_inf, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
    exact and_congr_right fun _ => eq_comm
  have hB₁K : ∀ c ∈ A ⊓ B, c ∈ K := fun c hc =>
    (hmemK c).mpr ⟨hBD (mem_inf.mp hc).2, (hyB c (mem_inf.mp hc).2).mpr (mem_inf.mp hc).1⟩
  have hyM : y ∈ egM B z := mem_egM_of_mem_normalizer (mem_inf.mp hyNL).1 hyz
  have hyD : ∀ d ∈ D, y * d * y⁻¹ ∈ D := hD.norm y hyM
  have hyD' : ∀ d ∈ D, y⁻¹ * d * y ∈ D := by
    intro d hd
    have h := hD.norm y⁻¹ (inv_mem hyM) d hd
    rwa [inv_inv] at h
  have hK16 : 16 ≤ Nat.card K := by
    have h : Nat.card (A ⊓ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) ≤ Nat.card K :=
      card_mul_card_le_of_const (S := (K : Set G)) (T := ((A ⊓ B : Subgroup G) : Set G))
        (U := ((A ⊓ B : Subgroup G) : Set G)) (fun g => z * g * z⁻¹ * g⁻¹)
        (fun c hc => by
          obtain ⟨d₀, hd₀, hc₀⟩ := hD.onto c (mem_inf.mp hc).2
          obtain ⟨d, hd, hyd, hτd⟩ := exists_fixed_comm_z hDc hyz hy3 hyD hyD' hzD hd₀ hc₀
            ((hyB c (mem_inf.mp hc).2).mpr (mem_inf.mp hc).1) (hD2 c (hBD (mem_inf.mp hc).2))
          exact ⟨d, (hmemK d).mpr ⟨hd, hyd⟩, hτd⟩)
        (fun s hs u hu => ⟨K.mul_mem hs (hB₁K u hu),
          comm_z_mul_of_eq_one (comm_z_eq_one_of_comm (hzL u (hBL u (mem_inf.mp hu).2)))⟩)
    rw [h4] at h
    omega
  have hZK : ∀ x ∈ Z, ∀ k ∈ K, x * k = k * x := by
    refine comm_of_closure hX hZel.2 ?_ hyZ fun k hk => ((hmemK k).mp hk).2
    rintro x ⟨hxZ, hx1, hx2⟩ k hk
    obtain ⟨hkD, hyk⟩ := (hmemK k).mp hk
    have hxz : x * z = z * x := hzL x (hAL x (hZA hxZ))
    have hxM : x ∈ egM B z :=
      mem_egM_of_mem_normalizer (mem_inf.mp (hF.A_le_NB (hZA hxZ))).1 hxz
    have hcomm := comm_mem_of_rank_two hDc hD2 hBD hD.comm_z hD.onto hker hxz (hZel.2 x hxZ)
      (hD.norm x hxM) hx1 hx2 hyz hyB hkD hyk
    have e : x * k * x⁻¹ = x * k * x⁻¹ * k⁻¹ * k := by group
    rw [e]
    exact K.mul_mem (hB₁K _ hcomm) hk
  have hKlam : ∀ k ∈ K, k ∈ egLam A z := by
    intro k hk
    obtain ⟨hkD, hyk⟩ := (hmemK k).mp hk
    have hkA : ∀ a ∈ A, a * k = k * a := by
      intro a ha
      obtain ⟨x, hx, b, hb, rfl⟩ := hAdec a ha
      have h1 := hZK x hx k hk
      have h2 := hDc b (hBD (mem_inf.mp hb).2) k hkD
      calc x * b * k = x * (b * k) := mul_assoc _ _ _
        _ = x * (k * b) := by rw [h2]
        _ = x * k * b := (mul_assoc _ _ _).symm
        _ = k * x * b := by rw [h1]
        _ = k * (x * b) := mul_assoc _ _ _
    have hkk : k⁻¹ = k := inv_eq_of_mul_eq_one_right (hD2 k hkD)
    have hτB : z * k * z⁻¹ * k⁻¹ ∈ B := hD.comm_z k hkD
    have hτA : z * k * z⁻¹ * k⁻¹ ∈ A := by
      rw [← hyB _ hτB, ← comm_z_conj hyz, hyk]
    have hconjA : ∀ a ∈ A, k * a * k⁻¹ ∈ A := fun a ha => by
      rw [← hkA a ha, mul_inv_cancel_right]
      exact ha
    have hz : ∃ a ∈ A, k * z * k⁻¹ = a * z :=
      ⟨(z * k * z⁻¹ * k⁻¹)⁻¹, A.inv_mem hτA, by group⟩
    show k ∈ egM A z ⊓ centralizer (A : Set G)
    refine mem_inf.mpr ⟨mem_egM_of hconjA (fun a ha => by simpa only [hkk] using hconjA a ha) hz
      (by simpa only [hkk] using hz), ?_⟩
    exact mem_centralizer_iff.mpr fun a ha => hkA a ha
  have hKC : ∀ k ∈ K, k ∈ C → k ∈ A ⊓ B := by
    intro k hk hkC
    have hkD := ((hmemK k).mp hk).1
    have hkk : k⁻¹ = k := inv_eq_of_mul_eq_one_right (hD2 k hkD)
    have h1 : z * k * z⁻¹ * k⁻¹ = 1 := by rw [hinv k hkC, hkk, hD2 k hkD]
    exact mem_inf.mpr ⟨hkerC k hkC h1, hker k hkD h1⟩
  have hKz : ∀ k ∈ K, ∀ k' ∈ K, k ∉ C → k' ∉ C → k⁻¹ * k' ∈ C := by
    intro k hk k' hk' hkC hk'C
    have h1 := (hC.lam_eq k (hKlam k hk)).resolve_left hkC
    have h2 := (hC.lam_eq k' (hKlam k' hk')).resolve_left hk'C
    have e : k⁻¹ * k' = (z * k)⁻¹ * (z * k') := by group
    rw [e]
    exact C.mul_mem (C.inv_mem h1) h2
  have h8 := card_le_add_of_forall hKC hKz
  rw [h4] at h8
  omega

end CFSG.EvenSporadicStandard.M24Std
