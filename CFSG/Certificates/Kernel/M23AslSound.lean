module

public import Certificates.Data.Kernel.M23AslK
public import CFSG.Certificates.Kernel.LocalQTDiagKSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExt
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExt
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermIso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExtCheck

public section

namespace CFSG.KC.M23Asl

open Equiv CFSG.KC.LQT CFSG.KC.LQT.L CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six

theorem yK_sound {n : ℕ} (hn : n ≤ 32) {N d : ℕ} (L A : List (Perm (Fin n))) {CL GA : List ℕ}
    (hL : L.map P.code = CL) (hA : A.map P.code = GA) (h : yK n CL N GA (bfsK n CL d) = true) :
    closedH (L.map RN.enc) (elts (RN.enc : Perm (Fin n) → RN n) d L) = true ∧
      (elts (RN.enc : Perm (Fin n) → RN n) d L).size = N ∧
      A.all (fun g => (elts (RN.enc : Perm (Fin n) → RN n) d L).contains (RN.enc g)) = true := by
  subst hL hA
  unfold yK at h
  rw [P.andB_iff, P.andB_iff, P.beq_iff, P.allL_map, LK.closedK_iff hn, LK.sizeK_eq hn] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  rw [List.all_eq_true]
  intro g hg
  exact Std.HashSet.contains_iff_mem.2 ((LK.memK_iff hn L d g).1 (h3 g hg))

theorem yxK_sound {n : ℕ} (hn : n ≤ 32) {N d : ℕ} (L A : List (Perm (Fin n))) (x : Perm (Fin n))
    {CL GA : List ℕ} {cx : ℕ} (hL : L.map P.code = CL) (hA : A.map P.code = GA)
    (hx : P.code x = cx) (h : yxK n CL N cx GA (bfsK n CL d) = true) :
    (elts (RN.enc : Perm (Fin n) → RN n) d L).contains (RN.enc x) = false ∧
      closedH (L.map RN.enc) (elts (RN.enc : Perm (Fin n) → RN n) d L) = true ∧
      (elts (RN.enc : Perm (Fin n) → RN n) d L).size = N ∧
      A.all (fun g => (elts (RN.enc : Perm (Fin n) → RN n) d L).contains (RN.enc g)) = true := by
  unfold yxK at h
  rw [P.andB_iff, P.notB_iff] at h
  refine ⟨?_, yK_sound hn L A hL hA h.2⟩
  subst hL hx
  rw [Bool.eq_false_iff]
  intro hc
  exact h.1 ((LK.memK_iff hn L d x).2 (Std.HashSet.contains_iff_mem.1 hc))

section DiagExt

variable {G H R S : Type} [Group G] [Group H] [Finite G] [Finite H] [Mul R] [One R]
  [DecidableEq R] [Hashable R] [Mul S] [One S] [DecidableEq S] [Hashable S]

theorem diagExtOK_of_diagOK {e₁ : G → R} {e₂ : H → S} (h₁ : IsEnc e₁) (h₂ : IsEnc e₂) {d : ℕ}
    {a : List G} {b : List H} {n : ℕ} (hc : diagOK e₁ e₂ d a b n = true) :
    diagExtOK e₁ e₂ d a b n n = true := by
  simp only [diagOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hca, hsa⟩, hcb⟩, hsb⟩, hcd⟩, hsd⟩, hlen⟩ := hc
  have hE := isEnc_prod h₁ h₂
  set D := Subgroup.closure {p : G × H | p ∈ a.zip b} with hDdef
  have hD : Nat.card D = n := by
    have := card_closure_of_closedH hE (a.zip b) d hcd
    unfold elts at hsd
    rw [this, hsd]
  have hB : Nat.card (Subgroup.closure {h | h ∈ b}) = n := by
    have := card_closure_of_closedH h₂ b d hcb
    unfold elts at hsb
    rw [this, hsb]
  have hsnd : D.map (MonoidHom.snd G H) = Subgroup.closure {h | h ∈ b} := by
    rw [hDdef, MonoidHom.map_closure]
    congr 1
    ext h
    simp only [Set.mem_image, Set.mem_ofPred_eq, MonoidHom.coe_snd]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (List.of_mem_zip hp).2
    · intro hh
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hh
      exact ⟨(a[k]'(by omega), b[k]), List.mem_iff_getElem.mpr ⟨k, by simp [List.length_zip]; omega,
        by simp⟩, rfl⟩
  let π₂ : ↥D →* ↥(Subgroup.closure {h | h ∈ b}) :=
    ((MonoidHom.snd G H).comp D.subtype).codRestrict _ (fun x => by
      rw [← hsnd]
      exact ⟨x.1, x.2, rfl⟩)
  have h2 : Function.Surjective π₂ := by
    rintro ⟨y, hy⟩
    rw [← hsnd] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hinj : Function.Injective π₂ := (h2.bijective_of_nat_card_le (by rw [hD, hB])).1
  have key : ∀ r ∈ elts (fun p : G × H => (e₁ p.1, e₂ p.2)) d (a.zip b), r.2 = 1 → r.1 = 1 := by
    intro r hr hr2
    unfold elts at hr
    obtain ⟨x, hx, rfl⟩ := bfsSet_sound hE (a.zip b) d r hr
    have hx2 : x.2 = 1 := h₂.inj (hr2.trans h₂.map_one.symm)
    have e : π₂ ⟨x, hx⟩ = π₂ 1 := by
      rw [map_one]
      exact Subtype.ext hx2
    have hx1 : x = 1 := congrArg Subtype.val (hinj e)
    rw [hx1]
    exact h₁.map_one
  have h11 : (1 : R) * 1 = 1 := by rw [← h₁.map_one, ← h₁.map_mul, one_mul]
  unfold diagExtOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_filter]
  refine ⟨⟨⟨⟨⟨⟨⟨hca, hsa⟩, hcb⟩, hsb⟩, hcd⟩, hsd⟩, hlen⟩, fun r hr => ?_⟩
  obtain ⟨hr1, hr2⟩ := hr
  rw [Std.HashSet.mem_toList] at hr1
  have e1 := key r hr1 (by simpa using hr2)
  refine ⟨by rw [e1, h11], fun s hs => ?_⟩
  obtain ⟨hs1, hs2⟩ := hs
  rw [Std.HashSet.mem_toList] at hs1
  rw [e1, key s hs1 (by simpa using hs2)]

end DiagExt

theorem diagExt_sound {n₁ n₂ : ℕ} (h₁ : n₁ ≤ 32) (h₂ : n₂ ≤ 32) {d N : ℕ}
    (A : List (Perm (Fin n₁))) (B : List (Perm (Fin n₂))) {GA GB : List ℕ}
    (hA : A.map P.code = GA) (hB : B.map P.code = GB) (h : diagK n₁ n₂ d GA GB N = true) :
    diagExtOK (RN.enc : Perm (Fin n₁) → RN n₁) (RN.enc : Perm (Fin n₂) → RN n₂) d A B N N =
      true := by
  subst hA hB
  exact diagExtOK_of_diagOK (rawIsEnc n₁) (rawIsEnc n₂) (CFSG.KC.LQT.CM.diag_sound h₁ h₂ A B h)

end CFSG.KC.M23Asl

end
