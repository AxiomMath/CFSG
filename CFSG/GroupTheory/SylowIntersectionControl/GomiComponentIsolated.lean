module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact23Sylow
public import CFSG.GroupTheory.SylowIntersectionControl.IsolatedTransfer
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedCore
import CFSG.GroupTheory.ConjugatePairSubnormality
import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
import CFSG.LocalAnalysis.SteinbergBQControlSylowPromotion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type} [Group G]

theorem normal_of_isDirectProduct {S : Set (Subgroup G)} {N : Subgroup G}
    (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) : N.Normal :=
  ⟨fun _ hy g => hN.conj_mem (hSG g) hy⟩

private def conjOrbit (H A : Subgroup G) : Set (Subgroup G) :=
  {B | ∃ h ∈ H, B = A.map (MulAut.conj h).toMonoidHom}

private theorem map_conj_one_eq (B : Subgroup G) :
    B.map (MulAut.conj (1 : G)).toMonoidHom = B := by
  ext y
  simp

private theorem self_mem_conjOrbit (H A : Subgroup G) : A ∈ conjOrbit H A :=
  ⟨1, one_mem H, (map_conj_one_eq A).symm⟩

private theorem conjOrbit_subset {S : Set (Subgroup G)} {H A : Subgroup G}
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hA : A ∈ S) :
    conjOrbit H A ⊆ S := by
  rintro _ ⟨h, -, rfl⟩
  exact hSG h A hA

private theorem map_conj_mem_conjOrbit {H A B : Subgroup G} (hB : B ∈ conjOrbit H A) {k : G}
    (hk : k ∈ H) : B.map (MulAut.conj k).toMonoidHom ∈ conjOrbit H A := by
  obtain ⟨h, hh, rfl⟩ := hB
  exact ⟨k * h, mul_mem hk hh, Subgroup.map_conj_map_conj A h k⟩

private theorem of_map_conj_mem_conjOrbit {H A B : Subgroup G} {k : G} (hk : k ∈ H)
    (hB : B.map (MulAut.conj k).toMonoidHom ∈ conjOrbit H A) : B ∈ conjOrbit H A := by
  have := map_conj_mem_conjOrbit hB (inv_mem hk)
  rwa [Subgroup.map_conj_map_conj, inv_mul_cancel, map_conj_one_eq] at this

private theorem sSup_conjOrbit_le {S : Set (Subgroup G)} {N H A : Subgroup G}
    (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hA : A ∈ S) :
    sSup (conjOrbit H A) ≤ N :=
  sSup_le fun _ hB => hN.le (conjOrbit_subset hSG hA hB)

private theorem conj_mul_inv_conj_mem {H A : Subgroup G} {d h u w : G}
    (hd : d ∈ normalizer ((H ⊓ normalizer (A : Set G) : Subgroup G) : Set G)) (hh : h ∈ H)
    (hu : u ∈ H) (hw : w ∈ H) (hv : w⁻¹ * h * u ∈ normalizer (A : Set G)) :
    h * (u * d * u⁻¹) * h⁻¹ * (w * d * w⁻¹)⁻¹ ∈ H := by
  have hvH : w⁻¹ * h * u ∈ H := mul_mem (mul_mem (inv_mem hw) hh) hu
  have hvI : (w⁻¹ * h * u)⁻¹ ∈ H ⊓ normalizer (A : Set G) := inv_mem (mem_inf.mpr ⟨hvH, hv⟩)
  have h1 : d * (w⁻¹ * h * u)⁻¹ * d⁻¹ ∈ H ⊓ normalizer (A : Set G) :=
    (mem_normalizer_iff.mp hd _).mp hvI
  have e : h * (u * d * u⁻¹) * h⁻¹ * (w * d * w⁻¹)⁻¹ =
      w * ((w⁻¹ * h * u) * (d * (w⁻¹ * h * u)⁻¹ * d⁻¹)) * w⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hw (mul_mem hvH (mem_inf.mp h1).1)) (inv_mem hw)

private theorem sq_mem_of_mul_sq_mem {H : Subgroup G} {x h : G}
    (hx : x ∈ normalizer (H : Set G)) (hh : h ∈ H) (h2 : (x * h) ^ 2 ∈ H) : x ^ 2 ∈ H := by
  have h1 : x * h * x⁻¹ ∈ H := (mem_normalizer_iff.mp hx h).mp hh
  have e : x ^ 2 = (x * h * x⁻¹)⁻¹ * ((x * h) ^ 2 * h⁻¹) := by
    rw [sq, sq]
    group
  rw [e]
  exact mul_mem (inv_mem h1) (mul_mem h2 (inv_mem hh))

private theorem mem_of_inv_mul_mem {M : Subgroup G} {a b : G} (h : a⁻¹ * b ∈ M) (hb : b ∈ M) :
    a ∈ M := by
  simpa using inv_mem (mul_mem h (inv_mem hb))

private theorem normalizer_inf_sup_eq {A I : Subgroup G} (hIA : I ≤ normalizer (A : Set G)) :
    normalizer (I : Set G) ⊓ (A ⊔ I) = A ⊓ normalizer (I : Set G) ⊔ I := by
  refine le_antisymm (fun y hy => ?_) (sup_le (le_inf inf_le_right
    (inf_le_left.trans le_sup_left)) (le_inf le_normalizer le_sup_right))
  obtain ⟨hyN, hy⟩ := mem_inf.mp hy
  rw [sup_comm, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right I A hIA] at hy
  obtain ⟨i, hi, a, ha, rfl⟩ := hy
  have haN : a ∈ normalizer (I : Set G) := by
    simpa using mul_mem (inv_mem (le_normalizer hi)) hyN
  exact mul_mem (mem_sup_right hi) (mem_sup_left ⟨ha, haN⟩)

private theorem inf_normalizer_inf_eq (H A : Subgroup G) :
    A ⊓ normalizer ((H ⊓ normalizer (A : Set G) : Subgroup G) : Set G) ⊓
      (H ⊓ normalizer (A : Set G)) = H ⊓ A := by
  have hKI : H ⊓ A ≤ H ⊓ normalizer (A : Set G) :=
    le_inf inf_le_left (inf_le_right.trans le_normalizer)
  exact le_antisymm (le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans inf_le_left))
    (le_inf (le_inf inf_le_right (hKI.trans le_normalizer)) hKI)

private theorem isPGroup_inf_centralizer {A I : Subgroup G} (hI : IsPGroup 2 I)
    (hIA : I ≤ normalizer (A : Set G)) (hZ : A ⊓ centralizer (A : Set G) = ⊥) :
    IsPGroup 2 ((A ⊔ I) ⊓ centralizer (A : Set G) : Subgroup G) := by
  rintro ⟨y, hy⟩
  obtain ⟨hyAI, hyC⟩ := mem_inf.mp hy
  have hyIA : y ∈ (I ⊔ A : Subgroup G) := sup_comm A I ▸ hyAI
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right I A hIA] at hyIA
  obtain ⟨i, hi, a, ha, rfl⟩ := hyIA
  obtain ⟨k, hk⟩ := hI ⟨i, hi⟩
  have hik : i ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hpow : ∀ m : ℕ, (i ^ m)⁻¹ * (i * a) ^ m ∈ A := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 := (mem_normalizer_iff.mp (inv_mem (hIA hi)) _).mp ih
      rw [inv_inv] at h1
      have e : (i ^ (m + 1))⁻¹ * (i * a) ^ (m + 1) =
          i⁻¹ * ((i ^ m)⁻¹ * (i * a) ^ m) * i * a := by
        rw [pow_succ, pow_succ]
        simp only [mul_inv_rev, mul_assoc]
      rw [e]
      exact mul_mem h1 ha
  have h1 : (i * a) ^ 2 ^ k ∈ A ⊓ centralizer (A : Set G) :=
    mem_inf.mpr ⟨by simpa [hik] using hpow (2 ^ k), pow_mem hyC _⟩
  rw [hZ, mem_bot] at h1
  exact ⟨k, Subtype.ext (by simpa using h1)⟩

private theorem inv_mul_mul_mem_normalizer {A B : Subgroup G} {h u w : G}
    (hu : B = A.map (MulAut.conj u).toMonoidHom)
    (hw : B.map (MulAut.conj h).toMonoidHom = A.map (MulAut.conj w).toMonoidHom) :
    w⁻¹ * h * u ∈ normalizer (A : Set G) := by
  refine mem_normalizer_iff_map_conj_eq.mpr ?_
  change A.map (MulAut.conj (w⁻¹ * h * u)).toMonoidHom = A
  rw [mul_assoc, ← Subgroup.map_conj_map_conj, ← Subgroup.map_conj_map_conj, ← hu, hw,
    Subgroup.map_conj_map_conj, inv_mul_cancel, map_conj_one_eq]

variable [Finite G]

private theorem mem_normalizer_of_forall_conj_mem {X : Subgroup G} {g : G}
    (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : g ∈ normalizer (X : Set G) := by
  let f : X → X := fun x => ⟨g * x * g⁻¹, h x x.2⟩
  have hf : Function.Surjective f := Finite.injective_iff_surjective.mp fun a b hab =>
    Subtype.ext (by simpa [f] using congrArg Subtype.val hab)
  refine mem_normalizer_iff.mpr fun x => ⟨h x, fun hx => ?_⟩
  obtain ⟨y, hy⟩ := hf ⟨_, hx⟩
  have hyx : (y : G) = x := by simpa [f] using congrArg Subtype.val hy
  exact hyx ▸ y.2


private theorem mem_normalizer_sSup {T : Set (Subgroup G)} {k : G}
    (h : ∀ B ∈ T, B.map (MulAut.conj k).toMonoidHom ∈ T) :
    k ∈ normalizer ((sSup T : Subgroup G) : Set G) := by
  have hle : (sSup T).map (MulAut.conj k).toMonoidHom ≤ sSup T :=
    map_le_iff_le_comap.mpr (sSup_le fun B hB => map_le_iff_le_comap.mp (le_sSup (h B hB)))
  exact mem_normalizer_of_forall_conj_mem fun x hx => hle ⟨x, hx, rfl⟩


variable {S : Set (Subgroup G)} {N H : Subgroup G}

theorem coord_mem_of_isPIsolatedOver (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H) {B : Subgroup G} (hB : B ∈ S) {y : G}
    (hyH : y ∈ H) (hyN : y ∈ N) : ((hN.coord hB ⟨y, hyN⟩ : B) : G) ∈ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := normal_of_isDirectProduct hN hSG
  exact projIn_le_of_forall_le hN (fun Y hY hYN => hiso.le_of_normalizer_le hH hY hYN)
    (fun u _ J hJ => hSG u J hJ) inf_le_right (hH.to_le inf_le_left)
    normalizer_le_normalizer_inf_of_normal hB
    ((hN.mem_projIn_iff hB).mpr ⟨⟨y, hyN⟩, ⟨hyH, hyN⟩, rfl⟩)

theorem coord_inv_mul_conj_mem (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H) {x : G} (hxN : x ∈ N)
    (hxH : x ∈ normalizer (H : Set G)) {h : G} (hh : h ∈ H) {B : Subgroup G} (hB : B ∈ S) :
    ((hN.coord (hSG h B hB) ⟨x, hxN⟩ : B.map (MulAut.conj h).toMonoidHom) : G)⁻¹ *
      (h * (hN.coord hB ⟨x, hxN⟩ : G) * h⁻¹) ∈ H := by
  have hn := normal_of_isDirectProduct hN hSG
  have hy : h * x * h⁻¹ ∈ N := hn.conj_mem x hxN h
  have hxy : x⁻¹ * (h * x * h⁻¹) ∈ H := by
    have : x⁻¹ * h * x ∈ H := by simpa using (mem_normalizer_iff.mp (inv_mem hxH) h).mp hh
    simpa [mul_assoc] using mul_mem this (inv_mem hh)
  have hc := coord_mem_of_isPIsolatedOver hN hSG hH hiso (hSG h B hB) hxy
    (mul_mem (inv_mem hxN) hy)
  rw [show (⟨x⁻¹ * (h * x * h⁻¹), mul_mem (inv_mem hxN) hy⟩ : N) =
    (⟨x, hxN⟩ : N)⁻¹ * ⟨h * x * h⁻¹, hy⟩ from rfl, map_mul, map_inv, coe_mul, coe_inv,
    hN.coord_conj (hSG h) hB hxN] at hc
  exact hc

theorem mem_normalizer_of_forall_coord (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) {x : G} (hxN : x ∈ N)
    (h : ∀ h ∈ H, ∀ (B : Subgroup G) (hB : B ∈ S), h * ((hN.coord hB ⟨x, hxN⟩ : B) : G) * h⁻¹ *
      ((hN.coord (hSG h B hB) ⟨x, hxN⟩ : B.map (MulAut.conj h).toMonoidHom) : G)⁻¹ ∈ H) :
    x ∈ normalizer (H : Set G) := by
  have hn := normal_of_isDirectProduct hN hSG
  refine mem_normalizer_of_forall_conj_mem fun k hk => ?_
  have hy : k⁻¹ * x * k⁻¹⁻¹ ∈ N := hn.conj_mem x hxN k⁻¹
  have hw : k⁻¹ * x * k⁻¹⁻¹ * x⁻¹ ∈ H := by
    refine hN.mem_of_coord_mem (mul_mem hy (inv_mem hxN)) fun J hJ => ?_
    set B := J.map (MulAut.conj k⁻¹⁻¹).toMonoidHom
    have hBS : B ∈ S := hSG _ J hJ
    have hJB : B.map (MulAut.conj k⁻¹).toMonoidHom = J := by
      rw [Subgroup.map_conj_map_conj, mul_inv_cancel]
      ext y
      simp
    rw [show (⟨k⁻¹ * x * k⁻¹⁻¹ * x⁻¹, mul_mem hy (inv_mem hxN)⟩ : N) =
      ⟨k⁻¹ * x * k⁻¹⁻¹, hy⟩ * (⟨x, hxN⟩ : N)⁻¹ from rfl, map_mul, map_inv, coe_mul, coe_inv,
      hN.coord_val_congr hJ (hSG k⁻¹ B hBS) hJB.symm, hN.coord_conj (hSG k⁻¹) hBS hxN,
      hN.coord_val_congr hJ (hSG k⁻¹ B hBS) hJB.symm]
    exact h k⁻¹ (inv_mem hk) B hBS
  simpa [mul_assoc] using mul_mem hk hw

theorem coord_mem_normalizer_of_isPIsolatedOver (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H) {A : Subgroup G} (hA : A ∈ S) {x : G}
    (hxN : x ∈ N) (hxH : x ∈ normalizer (H : Set G)) :
    ((hN.coord hA ⟨x, hxN⟩ : A) : G) ∈
      normalizer ((H ⊓ normalizer (A : Set G) : Subgroup G) : Set G) := by
  have haA := le_normalizer (hN.coord hA ⟨x, hxN⟩).2
  refine inv_mem_iff.mp (mem_normalizer_of_forall_conj_mem fun i hi => ?_)
  obtain ⟨hiH, hiA⟩ := mem_inf.mp hi
  have hc := coord_inv_mul_conj_mem hN hSG hH hiso hxN hxH hiH hA
  rw [hN.coord_val_congr (hSG i A hA) hA (mem_normalizer_iff_map_conj_eq.mp hiA) ⟨x, hxN⟩] at hc
  rw [inv_inv]
  exact mem_inf.mpr ⟨by simpa [mul_assoc] using mul_mem hc hiH,
    mul_mem (mul_mem (inv_mem haA) hiA) haA⟩

private theorem coord_eq_one_of_not_mem (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) {A : Subgroup G}
    (hA : A ∈ S) {B : Subgroup G} (hB : B ∈ S) (hBO : B ∉ conjOrbit H A) {x : G}
    (hx : x ∈ sSup (conjOrbit H A)) (hxN : x ∈ N) : ((hN.coord hB ⟨x, hxN⟩ : B) : G) = 1 := by
  have hsub : conjOrbit H A ⊆ S \ {B} := fun C hC =>
    ⟨conjOrbit_subset hSG hA hC, fun h => hBO (Set.mem_singleton_iff.mp h ▸ hC)⟩
  rw [(hN.coord_eq_one_iff hB _).mpr (sSup_le_sSup hsub hx)]
  rfl

private theorem mem_sSup_conjOrbit (hN : IsDirectProduct S N) {A : Subgroup G} {x : G}
    (hxN : x ∈ N)
    (h : ∀ (B : Subgroup G) (hB : B ∈ S), B ∉ conjOrbit H A →
      ((hN.coord hB ⟨x, hxN⟩ : B) : G) = 1) : x ∈ sSup (conjOrbit H A) :=
  hN.mem_of_coord_mem hxN fun B hB => by
    by_cases hBO : B ∈ conjOrbit H A
    · exact le_sSup hBO (hN.coord hB ⟨x, hxN⟩).2
    · rw [h B hB hBO]
      exact one_mem _

private noncomputable def coordHom (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H) {A : Subgroup G} (hA : A ∈ S) :
    ↥(sSup (conjOrbit H A) ⊓ normalizer (H : Set G)) →*
      ↥(A ⊓ normalizer ((H ⊓ normalizer (A : Set G) : Subgroup G) : Set G)) :=
  (A.subtype.comp ((hN.coord hA).comp (inclusion (inf_le_left.trans
    (sSup_conjOrbit_le hN hSG hA))))).codRestrict _ fun x =>
      mem_inf.mpr ⟨(hN.coord hA _).2,
        coord_mem_normalizer_of_isPIsolatedOver hN hSG hH hiso hA _ (mem_inf.mp x.2).2⟩

private theorem coordHom_surjective (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H) {A : Subgroup G} (hA : A ∈ S) :
    Function.Surjective (coordHom hN hSG hH hiso hA) := by
  classical
  rintro ⟨d, hd⟩
  obtain ⟨hdA, hdI⟩ := mem_inf.mp hd
  have hex : ∀ B ∈ conjOrbit H A, ∃ h ∈ H, B = A.map (MulAut.conj h).toMonoidHom :=
    fun _ hB => hB
  choose! c hcH hcB using hex
  have hAO := self_mem_conjOrbit H A
  have hcA : c A ∈ normalizer (A : Set G) := mem_normalizer_iff_map_conj_eq.mpr (hcB A hAO).symm
  have hcI : c A ∈ H ⊓ normalizer (A : Set G) := mem_inf.mpr ⟨hcH A hAO, hcA⟩
  obtain ⟨d₀, rfl⟩ : ∃ d₀, d = c A * d₀ * (c A)⁻¹ := ⟨(c A)⁻¹ * d * c A, by group⟩
  have hd₀A : d₀ ∈ A := by
    simpa [mul_assoc] using (mem_normalizer_iff.mp (inv_mem hcA) _).mp hdA
  have hd₀I : d₀ ∈ normalizer ((H ⊓ normalizer (A : Set G) : Subgroup G) : Set G) := by
    simpa [mul_assoc] using mul_mem (mul_mem (inv_mem (le_normalizer hcI)) hdI)
      (le_normalizer hcI)
  have hmem : ∀ B ∈ conjOrbit H A, c B * d₀ * (c B)⁻¹ ∈ B := fun B hB => by
    have h : c B * d₀ * (c B)⁻¹ ∈ A.map (MulAut.conj (c B)).toMonoidHom := ⟨d₀, hd₀A, rfl⟩
    rwa [← hcB B hB] at h
  let z : (J : S) → (J : Subgroup G) := fun J =>
    if hJ : (J : Subgroup G) ∈ conjOrbit H A then ⟨c J * d₀ * (c J)⁻¹, hmem J hJ⟩ else 1
  obtain ⟨x, hxN, hx⟩ : ∃ x : G, ∃ hxN : x ∈ N, (⟨x, hxN⟩ : N) = hN.equiv z :=
    ⟨_, (hN.equiv z).2, rfl⟩
  have hz : ∀ (B : Subgroup G) (hB : B ∈ S), ((hN.coord hB ⟨x, hxN⟩ : B) : G) =
      if B ∈ conjOrbit H A then c B * d₀ * (c B)⁻¹ else 1 := fun B hB => by
    rw [hx, hN.coord_equiv hB z]
    by_cases hBO : B ∈ conjOrbit H A <;> simp [z, hBO]
  have hxE : x ∈ sSup (conjOrbit H A) :=
    mem_sSup_conjOrbit hN hxN fun B hB hBO => by rw [hz B hB, if_neg hBO]
  have hxH : x ∈ normalizer (H : Set G) := by
    refine mem_normalizer_of_forall_coord hN hSG hxN fun h hh B hB => ?_
    rw [hz B hB, hz _ (hSG h B hB)]
    by_cases hBO : B ∈ conjOrbit H A
    · have hBh := map_conj_mem_conjOrbit hBO hh
      rw [if_pos hBO, if_pos hBh]
      exact conj_mul_inv_conj_mem hd₀I hh (hcH B hBO) (hcH _ hBh)
        (inv_mul_mul_mem_normalizer (hcB B hBO) (hcB _ hBh))
    · rw [if_neg hBO, if_neg fun h' => hBO (of_map_conj_mem_conjOrbit hh h')]
      simp
  refine ⟨⟨x, mem_inf.mpr ⟨hxE, hxH⟩⟩, Subtype.ext ?_⟩
  change ((hN.coord hA ⟨x, hxN⟩ : A) : G) = _
  rw [hz A hA, if_pos hAO]

private theorem coordHom_ker_le (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H) {A : Subgroup G} (hA : A ∈ S) :
    (coordHom hN hSG hH hiso hA).ker ≤
      (sSup (conjOrbit H A) ⊓ normalizer (H : Set G) ⊓ H).subgroupOf
        (sSup (conjOrbit H A) ⊓ normalizer (H : Set G)) := by
  rintro ⟨x, hxX⟩ hx
  obtain ⟨hxE, hxH⟩ := mem_inf.mp hxX
  have hxN : x ∈ N := sSup_conjOrbit_le hN hSG hA hxE
  have h1 : ((hN.coord hA ⟨x, hxN⟩ : A) : G) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  show x ∈ sSup (conjOrbit H A) ⊓ normalizer (H : Set G) ⊓ H
  refine mem_inf.mpr ⟨hxX, hN.mem_of_coord_mem hxN fun B hB => ?_⟩
  by_cases hBO : B ∈ conjOrbit H A
  · obtain ⟨u, hu, rfl⟩ := hBO
    have hc := coord_inv_mul_conj_mem hN hSG hH hiso hxN hxH hu hA
    rw [h1, mul_one, mul_inv_cancel, mul_one] at hc
    exact inv_mem_iff.mp hc
  · rw [coord_eq_one_of_not_mem hN hSG hA hB hBO hxE hxN]
    exact one_mem H

private theorem map_coordHom (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H) {A : Subgroup G} (hA : A ∈ S) :
    ((sSup (conjOrbit H A) ⊓ normalizer (H : Set G) ⊓ H).subgroupOf
      (sSup (conjOrbit H A) ⊓ normalizer (H : Set G))).map (coordHom hN hSG hH hiso hA) =
    (H ⊓ A).subgroupOf (A ⊓ normalizer ((H ⊓ normalizer (A : Set G) : Subgroup G) : Set G)) := by
  refine le_antisymm ?_ fun k hk => ?_
  · rintro _ ⟨⟨y, hyX⟩, hy, rfl⟩
    have hyN : y ∈ N := sSup_conjOrbit_le hN hSG hA (mem_inf.mp hyX).1
    have hyH : y ∈ H := (mem_inf.mp (mem_subgroupOf.mp hy)).2
    exact mem_subgroupOf.mpr (mem_inf.mpr
      ⟨coord_mem_of_isPIsolatedOver hN hSG hH hiso hA hyH hyN, (hN.coord hA ⟨y, hyN⟩).2⟩)
  · obtain ⟨hkH, hkA⟩ := mem_inf.mp (mem_subgroupOf.mp hk)
    have hkE : (k : G) ∈ sSup (conjOrbit H A) := le_sSup (self_mem_conjOrbit H A) hkA
    have hkX : (k : G) ∈ sSup (conjOrbit H A) ⊓ normalizer (H : Set G) :=
      mem_inf.mpr ⟨hkE, le_normalizer hkH⟩
    exact ⟨⟨k, hkX⟩, mem_subgroupOf.mpr (mem_inf.mpr ⟨hkX, hkH⟩),
      Subtype.ext (hN.coord_of_mem hA hkA)⟩

private theorem isSubnormal_sup_conjOrbit (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) {A : Subgroup G}
    (hA : A ∈ S) :
    ((sSup (conjOrbit H A) ⊓ normalizer (H : Set G) ⊔ H).subgroupOf
      (normalizer (H : Set G))).IsSubnormal := by
  have := normal_of_isDirectProduct hN hSG
  have hNE : N ≤ normalizer ((sSup (conjOrbit H A) : Subgroup G) : Set G) := fun n hn =>
    mem_normalizer_sSup fun B hB => by
      have h := mem_normalizer_iff_map_conj_eq.mp (hN.le_normalizer (conjOrbit_subset hSG hA hB) hn)
      exact (congrArg (· ∈ conjOrbit H A) h).mpr hB
  have hHE : H ≤ normalizer ((sSup (conjOrbit H A) : Subgroup G) : Set G) := fun k hk =>
    mem_normalizer_sSup fun B hB => map_conj_mem_conjOrbit hB hk
  have hWN : normalizer (H : Set G) ⊓ N ⊔ H ≤ normalizer (H : Set G) :=
    sup_le inf_le_left le_normalizer
  have hXW : sSup (conjOrbit H A) ⊓ normalizer (H : Set G) ⊔ H ≤ normalizer (H : Set G) ⊓ N ⊔ H :=
    sup_le_sup_right (le_inf inf_le_right (inf_le_left.trans (sSup_conjOrbit_le hN hSG hA))) H
  have h1 : ((normalizer (H : Set G) ⊓ N ⊔ H).subgroupOf (normalizer (H : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWN).mpr fun g hg => inf_normalizer_le_normalizer_sup _ _
      (mem_inf.mpr ⟨normalizer_le_normalizer_inf_of_normal (le_normalizer hg), hg⟩)
  have h2 : ((sSup (conjOrbit H A) ⊓ normalizer (H : Set G) ⊔ H).subgroupOf
      (normalizer (H : Set G) ⊓ N ⊔ H)).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer hXW).mpr (sup_le (fun g hg => ?_) fun h hh => ?_)
    · obtain ⟨hgH, hgN⟩ := mem_inf.mp hg
      exact inf_normalizer_le_normalizer_sup _ _ (mem_inf.mpr
        ⟨inf_normalizer_le_normalizer_inf (mem_inf.mpr ⟨hNE hgN, le_normalizer hgH⟩), hgH⟩)
    · exact inf_normalizer_le_normalizer_sup _ _ (mem_inf.mpr
        ⟨inf_normalizer_le_normalizer_inf (mem_inf.mpr ⟨hHE hh, le_normalizer (le_normalizer hh)⟩),
          le_normalizer hh⟩)
  exact isSubnormal_subgroupOf_trans hXW hWN h2.isSubnormal h1.isSubnormal

private theorem two_dvd_relIndex_inf_normalizer {A : Subgroup G} (hH : IsPGroup 2 H)
    (hKA : 2 ∣ (H ⊓ A).relIndex A) :
    2 ∣ (H ⊓ A).relIndex (A ⊓ normalizer ((H ⊓ normalizer (A : Set G) : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := inf_normalizer_inf_eq H A
  set I := H ⊓ normalizer (A : Set G) with hIdef
  have hIA : I ≤ normalizer (A : Set G) := inf_le_right
  have hID : I ≤ normalizer ((A ⊓ normalizer (I : Set G) : Subgroup G) : Set G) := fun i hi =>
    inf_normalizer_le_normalizer_inf (mem_inf.mpr ⟨hIA hi, le_normalizer (le_normalizer hi)⟩)
  have hK1 : I ⊓ A = H ⊓ A :=
    le_antisymm (inf_le_inf_right A inf_le_left)
      (le_inf (le_inf inf_le_left (inf_le_right.trans le_normalizer)) inf_le_right)
  have h1 : 2 ∣ I.relIndex (A ⊔ I) := by
    rw [sup_comm A I, (relIndex_sup_eq_relIndex_inf_of_le_normalizer hIA).1, hK1]
    exact hKA
  have h2 : 2 ∣ I.relIndex ((A ⊔ I) ⊓ normalizer (I : Set G)) := by
    by_contra h
    exact CFSG.LocalAnalysis.SteinbergBQ.not_dvd_relIndex_of_not_dvd_relIndex_normalizer
      le_sup_right (hH.to_le inf_le_left) h h1
  rwa [inf_comm (A ⊔ I), normalizer_inf_sup_eq hIA, sup_comm (A ⊓ _),
    (relIndex_sup_eq_relIndex_inf_of_le_normalizer hID).1, inf_comm I, hD] at h2

private theorem two_dvd_relIndex_sup (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H) {A : Subgroup G} (hA : A ∈ S)
    (hKA : 2 ∣ (H ⊓ A).relIndex A) :
    2 ∣ H.relIndex (sSup (conjOrbit H A) ⊓ normalizer (H : Set G) ⊔ H) := by
  have e : (sSup (conjOrbit H A) ⊓ normalizer (H : Set G) ⊓ H).relIndex
      (sSup (conjOrbit H A) ⊓ normalizer (H : Set G)) =
      (H ⊓ A).relIndex (A ⊓ normalizer ((H ⊓ normalizer (A : Set G) : Subgroup G) : Set G)) :=
    (index_map_eq _ (coordHom_surjective hN hSG hH hiso hA)
      (coordHom_ker_le hN hSG hH hiso hA)).symm.trans
      (congrArg index (map_coordHom hN hSG hH hiso hA))
  set X := sSup (conjOrbit H A) ⊓ normalizer (H : Set G) with hX
  have hHX : H ≤ normalizer (X : Set G) := fun h hh => inf_normalizer_le_normalizer_inf
    (mem_inf.mpr ⟨mem_normalizer_sSup fun B hB => map_conj_mem_conjOrbit hB hh,
      le_normalizer (le_normalizer hh)⟩)
  rw [sup_comm X H, (relIndex_sup_eq_relIndex_inf_of_le_normalizer hHX).1, inf_comm H X, e]
  exact two_dvd_relIndex_inf_normalizer hH hKA

theorem IsPIsolatedOver.inf_normalizer_of_component
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H) (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hH : IsPGroup 2 H)
    {A : Subgroup G} (hA : A ∈ S) (hKA : 2 ∣ (H ⊓ A).relIndex A) :
    IsPIsolatedOver 2 (A ⊓ normalizer ((H ⊓ normalizer (A : Set G) : Subgroup G) : Set G))
      (H ⊓ A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXH : sSup (conjOrbit H A) ⊓ normalizer (H : Set G) ≤ normalizer (H : Set G) :=
    inf_le_right
  have h1 := hiso.of_isSubnormal_le_over hH le_rfl le_sup_right le_rfl
    (sup_le hXH le_normalizer) (isSubnormal_sup_conjOrbit hN hSG hA)
    (two_dvd_relIndex_sup hN hSG hH hiso hA hKA)
  have h2 := (isPIsolatedOver_subgroupOf_iff inf_le_left le_rfl).mpr
    ((isPIsolatedOver_sup_iff hH hXH).mp h1)
  rw [subgroupOf_self] at h2
  have hf := coordHom_surjective hN hSG hH hiso hA
  have hk := coordHom_ker_le hN hSG hH hiso hA
  have h3 := (isPIsolatedOver_map_iff hf (((hH.to_le inf_le_right).comap_subtype).to_le hk) hk
    le_top).mpr h2
  rw [map_top_of_surjective _ hf, map_coordHom hN hSG hH hiso hA] at h3
  have hKD : H ⊓ A ≤ A ⊓ normalizer ((H ⊓ normalizer (A : Set G) : Subgroup G) : Set G) :=
    le_inf inf_le_right
      ((le_inf inf_le_left (inf_le_right.trans le_normalizer)).trans le_normalizer)
  exact (isPIsolatedOver_subgroupOf_iff hKD le_rfl).mp (by rwa [subgroupOf_self])

theorem IsPIsolatedOver.mem_of_component
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H) (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hH : IsPGroup 2 H)
    {A : Subgroup G} (hA : A ∈ S) (hKA : 2 ∣ (H ⊓ A).relIndex A) {M : Subgroup G} (hHM : H ≤ M)
    (hDM : ∀ d ∈ A ⊓ normalizer ((H ⊓ normalizer (A : Set G) : Subgroup G) : Set G),
      d ^ 2 ∈ H → d ∈ M)
    {a : G} (ha : a ∈ normalizer (H : Set G)) (ha2 : a ^ 2 ∈ H) : a ∈ M := by
  have hXH : sSup (conjOrbit H A) ⊓ normalizer (H : Set G) ≤ normalizer (H : Set G) :=
    inf_le_right
  have hmem := hiso.mem_of_isSubnormal_over hH le_normalizer le_rfl le_sup_right
    (sup_le hXH le_normalizer) (isSubnormal_sup_conjOrbit hN hSG hA)
    (two_dvd_relIndex_sup hN hSG hH hiso hA hKA) ha ha2
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ H hXH] at hmem
  obtain ⟨x, hxX, h, hh, rfl⟩ := hmem
  obtain ⟨hxE, hxH⟩ := mem_inf.mp hxX
  have hxN : x ∈ N := sSup_conjOrbit_le hN hSG hA hxE
  have hd : ((hN.coord hA ⟨x, hxN⟩ : A) : G) ∈ M := by
    refine hDM _ (mem_inf.mpr ⟨(hN.coord hA _).2,
      coord_mem_normalizer_of_isPIsolatedOver hN hSG hH hiso hA hxN hxH⟩) ?_
    have := coord_mem_of_isPIsolatedOver hN hSG hH hiso hA
      (sq_mem_of_mul_sq_mem hxH hh ha2) (pow_mem hxN 2)
    rwa [show (⟨x ^ 2, pow_mem hxN 2⟩ : N) = ⟨x, hxN⟩ ^ 2 from rfl, map_pow,
      SubgroupClass.coe_pow] at this
  refine mul_mem (hN.mem_of_coord_mem hxN fun B hB => ?_) (hHM hh)
  by_cases hBO : B ∈ conjOrbit H A
  · obtain ⟨u, hu, rfl⟩ := hBO
    exact mem_of_inv_mul_mem (hHM (coord_inv_mul_conj_mem hN hSG hH hiso hxN hxH hu hA))
      (mul_mem (mul_mem (hHM hu) hd) (inv_mem (hHM hu)))
  · rw [coord_eq_one_of_not_mem hN hSG hA hB hBO hxE hxN]
    exact one_mem M

theorem IsPIsolatedOver.normalizer_inf_sup_of_component
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H) (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hH : IsPGroup 2 H)
    {A : Subgroup G} (hA : A ∈ S) (hKA : 2 ∣ (H ⊓ A).relIndex A) :
    IsPIsolatedOver 2 (normalizer ((H ⊓ normalizer (A : Set G) : Subgroup G) : Set G) ⊓
      (A ⊔ H ⊓ normalizer (A : Set G))) (H ⊓ normalizer (A : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [normalizer_inf_sup_eq inf_le_right,
    isPIsolatedOver_sup_iff (hH.to_le inf_le_left) inf_le_right, inf_normalizer_inf_eq]
  exact hiso.inf_normalizer_of_component hN hSG hH hA hKA

theorem IsPIsolatedOver.sup_inf_centralizer_le_of_component
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H) (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hH : IsPGroup 2 H)
    {A : Subgroup G} (hA : A ∈ S) (hKA : 2 ∣ (H ⊓ A).relIndex A)
    (hZ : A ⊓ centralizer (A : Set G) = ⊥) :
    (A ⊔ H ⊓ normalizer (A : Set G)) ⊓ centralizer (A : Set G) ≤ H ⊓ normalizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI : IsPGroup 2 (H ⊓ normalizer (A : Set G) : Subgroup G) := hH.to_le inf_le_left
  have hIA : H ⊓ normalizer (A : Set G) ≤ normalizer (A : Set G) := inf_le_right
  refine (hiso.normalizer_inf_sup_of_component hN hSG hH hA hKA).le_of_inf_normalizer_le hI
    le_sup_right (isPGroup_inf_centralizer hI hIA hZ) inf_le_left fun g hg => ?_
  have hgAI := (mem_inf.mp hg).2
  have hgA : g ∈ normalizer (A : Set G) := sup_le le_normalizer hIA hgAI
  exact inf_normalizer_le_normalizer_inf (mem_inf.mpr ⟨le_normalizer hgAI,
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp inferInstance hgA⟩)

end CFSG.GroupTheory
