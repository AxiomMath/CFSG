module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step44Split

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Hexa CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native HeSylow

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem exists_add_omega : ∀ w < 16, ∃ v < 16, v ^^^ hexaOmega[v]! = w := by decide

theorem xor_lt_four : ∀ a < 4, ∀ b < 4, a ^^^ b < 4 := by decide

namespace PlaneData

variable (hD : PlaneData G A R g E F)
include hD

theorem mem_E_of_mem_centralizer {x : G} (hx : x ∈ F) (hxC : x ∈ centralizer (E : Set G)) :
    x ∈ E := by
  rw [hD.centralizer_eq] at hxC
  exact mem_of_mem_sup_odd (hD.isPGroup_sup.to_le le_sup_left) (AS76b.odd_card_oddCoreIn _)
    (hD.centralizer_eq ▸ le_sup_right) hxC (hD.sqF x hx)

theorem mem_oddCore_of_pow_odd {c : G} (hc : c ∈ centralizer (E : Set G)) {m : ℕ} (hm : Odd m)
    (hk : c ^ m = 1) : c ∈ AS76b.oddCoreIn (centralizer (A : Set G)) := by
  have hOE : AS76b.oddCoreIn (centralizer (A : Set G)) ≤ centralizer (E : Set G) :=
    hD.centralizer_eq ▸ le_sup_right
  have hN : E ≤ normalizer (AS76b.oddCoreIn (centralizer (A : Set G)) : Set G) := fun e he =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun o ho =>
      (mem_centralizer_iff.mp (hOE ho) e he).symm)
  rw [hD.centralizer_eq] at hc
  have hc' : c ∈ ((E ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) : Subgroup G) : Set G) := hc
  rw [coe_mul_of_left_le_normalizer_right _ _ hN] at hc'
  obtain ⟨e, he, o, ho, rfl⟩ := hc'
  have hcomm : Commute e o := mem_centralizer_iff.mp (hOE ho) e he
  have he3 : e ^ m = e := by
    have he2 : e ^ 2 = 1 := by rw [sq]; exact hD.sqE e he
    obtain ⟨k, hk⟩ := hm
    rw [hk, pow_succ, pow_mul, he2, one_pow, one_mul]
  have h1 : e ^ m * o ^ m = 1 := by rw [← hcomm.mul_pow]; exact hk
  rw [he3] at h1
  have heO : e ∈ AS76b.oddCoreIn (centralizer (A : Set G)) := by
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem (pow_mem ho _)
  have hEO : E ⊓ AS76b.oddCoreIn (centralizer (A : Set G)) = ⊥ :=
    two_subgroup_of_odd_eq_bot _ _ ((hD.isPGroup_sup.to_le le_sup_left).to_le inf_le_left)
      (AS76b.odd_card_oddCoreIn _) inf_le_right
  have he1 : e = 1 := by
    have h2 : e ∈ E ⊓ AS76b.oddCoreIn (centralizer (A : Set G)) := ⟨he, heO⟩
    rwa [hEO, mem_bot] at h2
  simpa [he1] using ho

end PlaneData

section Theta

variable (hc15 : hexaCheck = true) (hS : hexaStabCheck = true) (h44 : step44Check = true)
  (hD : PlaneData G A R g E F) {rep : Fin 64 → G} (hc : HexaCoord E R (pointsIn R E) rep)
  (hRg : ∀ v, rep v ∈ rightConjugate R g ↔ v.val ∈ hexaOval[1]!)

section T1

variable {t₁ : G} (ht₁N : t₁ ∈ normalizer (E : Set G)) (ht₁ : hc.psi ⟨t₁, ht₁N⟩ = omegaP)
include hc15 h44 ht₁

omit [Finite G] in
theorem eq_one_of_mem_E_comm {x : G} (hx : x ∈ E) (hxt : t₁ * x = x * t₁) : x = 1 := by
  obtain ⟨v, rfl⟩ := hc.surj x hx
  have h3 : rep (omegaP v) = rep v := by
    rw [← ht₁, hc.rep_psi]
    show t₁ * rep v * t₁⁻¹ = rep v
    rw [hxt, mul_inv_cancel_right]
  rw [eq_zero_of_omegaP_fix hc15 h44 (hc.inj h3), hc.rep_zero]

include hD

theorem eq_of_psi_eq_of_comm {f f' : G} (hf : f ∈ F) (hf' : f' ∈ F) (hft : t₁ * f = f * t₁)
    (hf't : t₁ * f' = f' * t₁)
    (h : hc.psi ⟨f, hD.F_le_normalizer hf⟩ = hc.psi ⟨f', hD.F_le_normalizer hf'⟩) : f = f' := by
  have hker : (⟨f, hD.F_le_normalizer hf⟩ : ↥(normalizer (E : Set G)))⁻¹ *
      ⟨f', hD.F_le_normalizer hf'⟩ ∈ hc.psi.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hC : f⁻¹ * f' ∈ centralizer (E : Set G) := (hc.psi_eq_one_iff _).1 hker
  have hE := hD.mem_E_of_mem_centralizer (mul_mem (inv_mem hf) hf') hC
  have hcomm : t₁ * (f⁻¹ * f') = (f⁻¹ * f') * t₁ :=
    ((Commute.inv_right (show Commute t₁ f from hft)).mul_right hf't).eq
  have h1 := eq_one_of_mem_E_comm hc15 h44 hc ht₁N ht₁ hE hcomm
  rw [inv_mul_eq_one] at h1
  exact h1

include hS hRg

theorem exists_mem_F_comm (ht₁F : t₁ ∈ normalizer (F : Set G)) {m : ℕ} (hm : m < 4) :
    ∃ f, ∃ hf : f ∈ F, t₁ * f = f * t₁ ∧ hc.psi ⟨f, hD.F_le_normalizer hf⟩ = v0P m := by
  obtain ⟨f', hf', hf'm⟩ := exists_mem_F_psi_eq hc15 hS h44 hD hc hRg hm
  have hf'N := hD.F_le_normalizer hf'
  have hu : f'⁻¹ * (t₁ * f' * t₁⁻¹) ∈ E ⊓ F := by
    have hFt : t₁ * f' * t₁⁻¹ ∈ F := (mem_normalizer_iff.mp ht₁F f').mp hf'
    have hker : (⟨f', hf'N⟩ : ↥(normalizer (E : Set G)))⁻¹ *
        (⟨t₁, ht₁N⟩ * ⟨f', hf'N⟩ * ⟨t₁, ht₁N⟩⁻¹) ∈ hc.psi.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, ht₁, hf'm,
        omegaP_comm_v0P hc15 h44 hm, mul_inv_cancel_right, inv_mul_cancel]
    have hC : f'⁻¹ * (t₁ * f' * t₁⁻¹) ∈ centralizer (E : Set G) := (hc.psi_eq_one_iff _).1 hker
    have hF : f'⁻¹ * (t₁ * f' * t₁⁻¹) ∈ F := mul_mem (inv_mem hf') hFt
    exact ⟨hD.mem_E_of_mem_centralizer hF hC, hF⟩
  obtain ⟨w, hw⟩ := hc.surj _ hu.1
  have hw16 : w.val < 16 := (rep_mem_inf_iff hD hc hRg w).1 (hw ▸ hu)
  obtain ⟨v, hv16, hvw⟩ := exists_add_omega w.val hw16
  have hωv : hexaOmega[v]! = (omegaP ⟨v, by omega⟩).val := (rep_omega hc15 h44).1.apply (by omega)
  have hxw : xorF w (omegaP ⟨v, by omega⟩) = ⟨v, by omega⟩ := by
    apply Fin.ext
    rw [val_xorF, ← hvw, hωv, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have hvE : rep ⟨v, by omega⟩ ∈ E ⊓ F := (rep_mem_inf_iff hD hc hRg _).2 hv16
  refine ⟨f' * rep ⟨v, by omega⟩, mul_mem hf' hvE.2, ?_, ?_⟩
  · have h1 : t₁ * rep ⟨v, by omega⟩ * t₁⁻¹ = rep (omegaP ⟨v, by omega⟩) := by
      rw [← ht₁, hc.rep_psi]
    have h2 : t₁ * f' * t₁⁻¹ = f' * rep w := by
      rw [hw]
      group
    calc t₁ * (f' * rep ⟨v, by omega⟩) =
        (t₁ * f' * t₁⁻¹) * (t₁ * rep ⟨v, by omega⟩ * t₁⁻¹) * t₁ := by group
      _ = f' * (rep w * rep (omegaP ⟨v, by omega⟩)) * t₁ := by rw [h2, h1]; group
      _ = f' * rep ⟨v, by omega⟩ * t₁ := by rw [← hc.add, hxw]
  · have hvC : hc.psi ⟨rep ⟨v, by omega⟩, hD.F_le_normalizer hvE.2⟩ = 1 :=
      (hc.psi_eq_one_iff _).2 (mem_centralizer_iff.mpr fun x hx => hD.commE x hx _ hvE.1)
    have e : (⟨f' * rep ⟨v, by omega⟩, hD.F_le_normalizer (mul_mem hf' hvE.2)⟩ :
        ↥(normalizer (E : Set G))) = ⟨f', hf'N⟩ * ⟨rep ⟨v, by omega⟩, hD.F_le_normalizer hvE.2⟩ :=
      rfl
    rw [e, map_mul, hvC, mul_one, hf'm]

end T1

include hc15 h44 in
omit [Finite G] in
theorem omegaP_comm_of_mem_om9 {x : Equiv.Perm (Fin 64)} (hx : x ∈ om9) :
    x * omegaP = omegaP * x := by
  obtain ⟨a, b, rfl⟩ := exists_eq_of_mem_om9 hc15 h44 hx
  have h1 : muP ^ b * omegaP = omegaP * muP ^ b :=
    (Commute.pow_left (show Commute muP omegaP from muP_comm_omegaP hc15 h44) b).eq
  calc omegaP ^ a * muP ^ b * omegaP = omegaP ^ a * (muP ^ b * omegaP) := mul_assoc _ _ _
    _ = omegaP ^ a * (omegaP * muP ^ b) := by rw [h1]
    _ = (omegaP ^ a * omegaP) * muP ^ b := (mul_assoc _ _ _).symm
    _ = (omegaP * omegaP ^ a) * muP ^ b := by rw [(Commute.self_pow omegaP a).eq]
    _ = omegaP * (omegaP ^ a * muP ^ b) := mul_assoc _ _ _

include hc15 h44 in
omit [Finite G] in
theorem muP_pow_conj_v0P (b : ℕ) {m : ℕ} (hm : m < 4) :
    muP ^ b * v0P m * (muP ^ b)⁻¹ = v0P (muPiN b m) ∧ muPiN b m < 4 := by
  induction b with
  | zero => simp [muPiN, hm]
  | succ b ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, muPi_lt h44 h2⟩
    have e : muP ^ (b + 1) * v0P m * (muP ^ (b + 1))⁻¹ =
        muP * (muP ^ b * v0P m * (muP ^ b)⁻¹) * muP⁻¹ := by
      rw [pow_succ']
      group
    rw [e, h1, muP_conj_v0P hc15 h44 h2]
    rfl

include hc15 h44 in
omit [Finite G] in
theorem smTau_parts {a b : ℕ} (ha : a < 3) (hb : b < 3) (i : Fin 256) :
    smTau a b i.val % 64 = ((omegaP ^ a * muP ^ b) ⟨i.val % 64, Nat.mod_lt _ (by norm_num)⟩).val ∧
      smTau a b i.val / 64 = muPiN b (i.val / 64) := by
  have hrep : Rep 64 (omuA a b) (omegaP ^ a * muP ^ b) := by
    have h := rep_mulN (rep_powN (rep_omega hc15 h44).1 (a % 3))
      (rep_powN (rep_mu hc15 h44).1 (b % 3))
    have e : omegaP ^ (a % 3) * muP ^ (b % 3) = omegaP ^ a * muP ^ b := by
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    rw [e] at h
    exact h
  have h1 : (omuA a b)[i.val % 64]! =
      ((omegaP ^ a * muP ^ b) ⟨i.val % 64, Nat.mod_lt _ (by norm_num)⟩).val :=
    hrep.apply (Nat.mod_lt _ (by norm_num))
  have h2 := ((omegaP ^ a * muP ^ b) ⟨i.val % 64, Nat.mod_lt _ (by norm_num)⟩).2
  unfold smTau
  rw [h1, Nat.mod_eq_of_lt hb]
  constructor <;> omega

section TData

variable {T : Subgroup G} (hTK : T ≤ kPrime hc) (hT3 : IsPGroup 3 T)
  (hTψ : (T.subgroupOf (normalizer (E : Set G))).map hc.psi = om9)

include hTψ in
omit [Finite G] in
theorem psi_mem_om9_of_mem {t : G} (ht : t ∈ T) :
    hc.psi ⟨t, kPrime_le_normalizer hc (hTK ht)⟩ ∈ om9 := by
  rw [← hTψ]
  exact Subgroup.mem_map_of_mem hc.psi (show (⟨t, kPrime_le_normalizer hc (hTK ht)⟩ :
    ↥(normalizer (E : Set G))) ∈ T.subgroupOf (normalizer (E : Set G)) from ht)

include hc15 h44 hD hT3 hTψ in
theorem comm_conj_of_comm {t₁ t f : G} (ht₁T : t₁ ∈ T)
    (ht₁ : hc.psi ⟨t₁, kPrime_le_normalizer hc (hTK ht₁T)⟩ = omegaP) (htT : t ∈ T) (hf : f ∈ F)
    (hft : t₁ * f = f * t₁) : t₁ * (t * f * t⁻¹) = (t * f * t⁻¹) * t₁ := by
  have htN : t ∈ normalizer (E : Set G) := kPrime_le_normalizer hc (hTK htT)
  have ht₁N : t₁ ∈ normalizer (E : Set G) := kPrime_le_normalizer hc (hTK ht₁T)
  have hcT : t₁⁻¹ * (t⁻¹ * t₁ * t) ∈ T :=
    mul_mem (inv_mem ht₁T) (mul_mem (mul_mem (inv_mem htT) ht₁T) htT)
  have hcN : t₁⁻¹ * (t⁻¹ * t₁ * t) ∈ normalizer (E : Set G) :=
    mul_mem (inv_mem ht₁N) (mul_mem (mul_mem (inv_mem htN) ht₁N) htN)
  have hψc : hc.psi ⟨_, hcN⟩ = 1 := by
    have e : (⟨_, hcN⟩ : ↥(normalizer (E : Set G))) =
        (⟨t₁, ht₁N⟩)⁻¹ * ((⟨t, htN⟩)⁻¹ * ⟨t₁, ht₁N⟩ * ⟨t, htN⟩) := rfl
    have hψt := psi_mem_om9_of_mem hc hTK hTψ htT
    rw [e, map_mul, map_inv, map_mul, map_mul, map_inv, ht₁, mul_assoc (hc.psi ⟨t, htN⟩)⁻¹,
      ← omegaP_comm_of_mem_om9 hc15 h44 hψt, inv_mul_cancel_left, inv_mul_cancel]
  have hcC : t₁⁻¹ * (t⁻¹ * t₁ * t) ∈ centralizer (E : Set G) := (hc.psi_eq_one_iff _).1 hψc
  obtain ⟨k, hk⟩ := hT3 ⟨_, hcT⟩
  have hk' : (t₁⁻¹ * (t⁻¹ * t₁ * t)) ^ 3 ^ k = 1 := congrArg Subtype.val hk
  have hcO := hD.mem_oddCore_of_pow_odd hcC ((by norm_num : Odd 3).pow) hk'
  have hcF : t₁⁻¹ * (t⁻¹ * t₁ * t) ∈ centralizer (F : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right)
      (hD.oddCore_le_centralizer hcO)
  have hfc := mem_centralizer_iff.mp hcF f hf
  have key : (t⁻¹ * t₁ * t) * f = f * (t⁻¹ * t₁ * t) := by
    have e1 : t⁻¹ * t₁ * t = t₁ * (t₁⁻¹ * (t⁻¹ * t₁ * t)) := by group
    rw [e1]
    calc t₁ * (t₁⁻¹ * (t⁻¹ * t₁ * t)) * f = t₁ * ((t₁⁻¹ * (t⁻¹ * t₁ * t)) * f) :=
          mul_assoc _ _ _
      _ = t₁ * (f * (t₁⁻¹ * (t⁻¹ * t₁ * t))) := by rw [hfc]
      _ = (t₁ * f) * (t₁⁻¹ * (t⁻¹ * t₁ * t)) := (mul_assoc _ _ _).symm
      _ = (f * t₁) * (t₁⁻¹ * (t⁻¹ * t₁ * t)) := by rw [hft]
      _ = f * (t₁ * (t₁⁻¹ * (t⁻¹ * t₁ * t))) := mul_assoc _ _ _
  calc t₁ * (t * f * t⁻¹) = t * ((t⁻¹ * t₁ * t) * f) * t⁻¹ := by group
    _ = t * (f * (t⁻¹ * t₁ * t)) * t⁻¹ := by rw [key]
    _ = (t * f * t⁻¹) * t₁ := by group


omit [Finite G] in
theorem div64_lt (i : Fin 256) : i.val / 64 < 4 := by omega

@[expose] def vecPart (i : Fin 256) : Fin 64 := ⟨i.val % 64, Nat.mod_lt _ (by norm_num)⟩

@[expose] def thetaS (rep : Fin 64 → G) (f₀ : ℕ → G) (i : Fin 256) : G :=
  rep (vecPart i) * f₀ (i.val / 64)

section ThetaS

variable {t₁ : G} (ht₁T : t₁ ∈ T)
  (ht₁ : hc.psi ⟨t₁, kPrime_le_normalizer hc (hTK ht₁T)⟩ = omegaP)
  {f₀ : ℕ → G} (hf₀F : ∀ m < 4, f₀ m ∈ F) (hf₀t : ∀ m < 4, t₁ * f₀ m = f₀ m * t₁)
  (hf₀ψ : ∀ m (hm : m < 4), hc.psi ⟨f₀ m, hD.F_le_normalizer (hf₀F m hm)⟩ = v0P m)

omit [Finite G] in
include hc hf₀F in
theorem thetaS_mem (i : Fin 256) : thetaS rep f₀ i ∈ E ⊔ F :=
  mul_mem (mem_sup_left (hc.mem _)) (mem_sup_right (hf₀F _ (div64_lt i)))

include hc15 h44 hD ht₁ hf₀t hf₀ψ in
theorem f0_mul {m m' : ℕ} (hm : m < 4) (hm' : m' < 4) : f₀ m * f₀ m' = f₀ (m ^^^ m') := by
  have hmm := xor_lt_four m hm m' hm'
  refine eq_of_psi_eq_of_comm hc15 h44 hD hc _ ht₁ (mul_mem (hf₀F m hm) (hf₀F m' hm'))
    (hf₀F _ hmm) ((show Commute t₁ (f₀ m) from hf₀t m hm).mul_right (hf₀t m' hm')).eq
    (hf₀t _ hmm) ?_
  have e : (⟨f₀ m * f₀ m', hD.F_le_normalizer (mul_mem (hf₀F m hm) (hf₀F m' hm'))⟩ :
      ↥(normalizer (E : Set G))) =
      ⟨f₀ m, hD.F_le_normalizer (hf₀F m hm)⟩ * ⟨f₀ m', hD.F_le_normalizer (hf₀F m' hm')⟩ := rfl
  rw [e, map_mul, hf₀ψ m hm, hf₀ψ m' hm', hf₀ψ _ hmm, v0P_mul hc15 h44 hm hm']

include hc15 h44 hD ht₁ hf₀t hf₀ψ in
theorem thetaS_mul (i j : Fin 256) :
    thetaS rep f₀ (smStarF i j) = thetaS rep f₀ i * thetaS rep f₀ j := by
  have hm := div64_lt i
  have hm' := div64_lt j
  have hv : (v0A (i.val / 64))[j.val % 64]! = (v0P (i.val / 64) (vecPart j)).val :=
    (rep_v0A hc15 h44 hm).2.1.apply _
  have hlt := (v0P (i.val / 64) (vecPart j)).2
  have hx : (i.val % 64) ^^^ (v0P (i.val / 64) (vecPart j)).val < 64 :=
    Nat.xor_lt_two_pow (n := 6) (Nat.mod_lt _ (by norm_num)) hlt
  have hsm : smStar i j = ((i.val % 64) ^^^ (v0P (i.val / 64) (vecPart j)).val) +
      64 * ((i.val / 64) ^^^ (j.val / 64)) := by
    unfold smStar
    rw [hv]
  have hvec : vecPart (smStarF i j) = xorF (vecPart i) (v0P (i.val / 64) (vecPart j)) := by
    apply Fin.ext
    show (smStar i j) % 64 = _
    rw [hsm, val_xorF]
    show _ = (i.val % 64) ^^^ _
    omega
  have hdiv : (smStarF i j).val / 64 = (i.val / 64) ^^^ (j.val / 64) := by
    show (smStar i j) / 64 = _
    rw [hsm]
    omega
  unfold thetaS
  rw [hvec, hdiv, hc.add, ← f0_mul hc15 h44 hD hc hTK ht₁T ht₁ hf₀F hf₀t hf₀ψ hm hm']
  have hconj : f₀ (i.val / 64) * rep (vecPart j) * (f₀ (i.val / 64))⁻¹ =
      rep (v0P (i.val / 64) (vecPart j)) := by
    rw [← hf₀ψ _ hm, hc.rep_psi]
  rw [← hconj]
  group

include hc15 h44 hD ht₁ hf₀t hf₀ψ in
theorem thetaS_injective : Function.Injective (thetaS rep f₀) := by
  intro i j hij
  unfold thetaS at hij
  have hm := div64_lt i
  have hm' := div64_lt j
  have hx : (rep (vecPart j))⁻¹ * rep (vecPart i) = f₀ (j.val / 64) * (f₀ (i.val / 64))⁻¹ := by
    calc (rep (vecPart j))⁻¹ * rep (vecPart i) =
        (rep (vecPart j))⁻¹ * (rep (vecPart i) * f₀ (i.val / 64)) * (f₀ (i.val / 64))⁻¹ := by
          group
      _ = (rep (vecPart j))⁻¹ * (rep (vecPart j) * f₀ (j.val / 64)) * (f₀ (i.val / 64))⁻¹ := by
          rw [hij]
      _ = _ := by group
  have hxE : (rep (vecPart j))⁻¹ * rep (vecPart i) ∈ E := mul_mem (inv_mem (hc.mem _)) (hc.mem _)
  have hcomm : t₁ * ((rep (vecPart j))⁻¹ * rep (vecPart i)) =
      ((rep (vecPart j))⁻¹ * rep (vecPart i)) * t₁ := by
    rw [hx]
    exact ((show Commute t₁ _ from hf₀t _ hm').mul_right
      (Commute.inv_right (show Commute t₁ _ from hf₀t _ hm))).eq
  have h1 := eq_one_of_mem_E_comm hc15 h44 hc _ ht₁ hxE hcomm
  rw [inv_mul_eq_one] at h1
  have hv := hc.inj h1.symm
  have hf : f₀ (i.val / 64) = f₀ (j.val / 64) := by
    rw [h1] at hij
    exact mul_left_cancel hij
  have hψ : v0P (i.val / 64) = v0P (j.val / 64) := by
    have e : (⟨f₀ (i.val / 64), hD.F_le_normalizer (hf₀F _ hm)⟩ : ↥(normalizer (E : Set G))) =
        ⟨f₀ (j.val / 64), hD.F_le_normalizer (hf₀F _ hm')⟩ := Subtype.ext hf
    rw [← hf₀ψ _ hm, ← hf₀ψ _ hm', e]
  have hmm := v0P_injOn hc15 h44 hm hm' hψ
  have hvv : i.val % 64 = j.val % 64 := congrArg Fin.val hv
  ext
  omega

include hc15 h44 hD ht₁ hf₀t hf₀ψ in
theorem thetaS_mem_E_iff (i : Fin 256) : thetaS rep f₀ i ∈ E ↔ i.val < 64 := by
  have hm := div64_lt i
  unfold thetaS
  rw [Subgroup.mul_mem_cancel_left _ (hc.mem _)]
  constructor
  · intro hE
    have h1 := eq_one_of_mem_E_comm hc15 h44 hc _ ht₁ hE (hf₀t _ hm)
    have h2 : v0P (i.val / 64) = 1 := by
      have e : (⟨f₀ (i.val / 64), hD.F_le_normalizer (hf₀F _ hm)⟩ :
          ↥(normalizer (E : Set G))) = 1 := Subtype.ext h1
      rw [← hf₀ψ _ hm, e, map_one]
    by_contra hge
    exact v0P_ne_one hc15 h44 hm (by omega) h2
  · intro hlt
    have h0 : i.val / 64 = 0 := by omega
    have hC : f₀ (i.val / 64) ∈ centralizer (E : Set G) :=
      (hc.psi_eq_one_iff _).1 (by rw [hf₀ψ _ hm, h0, v0P_zero hc15 h44])
    exact hD.mem_E_of_mem_centralizer (hf₀F _ hm) hC

include hc15 hS h44 hD hRg ht₁ hf₀t hf₀ψ hT3 hTψ in
theorem thetaS_tau {t : G} (htT : t ∈ T) {a b : ℕ} (ha : a < 3) (hb : b < 3)
    (ht : hc.psi ⟨t, kPrime_le_normalizer hc (hTK htT)⟩ = omegaP ^ a * muP ^ b) (i : Fin 256) :
    t * thetaS rep f₀ i * t⁻¹ = thetaS rep f₀ (smTauF a b i) := by
  have htN := kPrime_le_normalizer hc (hTK htT)
  have htF : t ∈ normalizer (F : Set G) :=
    hD.mem_normalizer_F (kPrime_le_normalizer_sup hc15 hS h44 hD hc hRg (hTK htT)) htN
  obtain ⟨hpart1, hpart2⟩ := smTau_parts hc15 h44 ha hb i
  have hm := div64_lt i
  have hmb := (muP_pow_conj_v0P hc15 h44 b hm).2
  have hvec : vecPart (smTauF a b i) = (omegaP ^ a * muP ^ b) (vecPart i) := Fin.ext hpart1
  have hdiv : (smTauF a b i).val / 64 = muPiN b (i.val / 64) := hpart2
  unfold thetaS
  rw [hvec, hdiv]
  have h1 : t * rep (vecPart i) * t⁻¹ = rep ((omegaP ^ a * muP ^ b) (vecPart i)) := by
    rw [← ht, hc.rep_psi]
  have h2 : t * f₀ (i.val / 64) * t⁻¹ = f₀ (muPiN b (i.val / 64)) := by
    have hF : t * f₀ (i.val / 64) * t⁻¹ ∈ F := (mem_normalizer_iff.mp htF _).mp (hf₀F _ hm)
    refine eq_of_psi_eq_of_comm hc15 h44 hD hc _ ht₁ hF (hf₀F _ hmb)
      (comm_conj_of_comm hc15 h44 hD hc hTK hT3 hTψ ht₁T ht₁ htT (hf₀F _ hm) (hf₀t _ hm))
      (hf₀t _ hmb) ?_
    have e : (⟨t * f₀ (i.val / 64) * t⁻¹, hD.F_le_normalizer hF⟩ : ↥(normalizer (E : Set G))) =
        ⟨t, htN⟩ * ⟨f₀ (i.val / 64), hD.F_le_normalizer (hf₀F _ hm)⟩ * (⟨t, htN⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, ht, hf₀ψ _ hm, hf₀ψ _ hmb]
    have e2 : omegaP ^ a * muP ^ b * v0P (i.val / 64) * (omegaP ^ a * muP ^ b)⁻¹ =
        omegaP ^ a * (muP ^ b * v0P (i.val / 64) * (muP ^ b)⁻¹) * (omegaP ^ a)⁻¹ := by group
    rw [e2, (muP_pow_conj_v0P hc15 h44 b hm).1,
      (Commute.pow_left (show Commute omegaP _ from omegaP_comm_v0P hc15 h44 hmb) a).eq,
      mul_inv_cancel_right]
  calc t * (rep (vecPart i) * f₀ (i.val / 64)) * t⁻¹ =
      (t * rep (vecPart i) * t⁻¹) * (t * f₀ (i.val / 64) * t⁻¹) := by group
    _ = _ := by rw [h1, h2]

end ThetaS

include hc15 hS h44 hD hRg hTK hT3 hTψ in
theorem exists_thetaS : ∃ Θ : Fin 256 → G, (∀ i, Θ i ∈ E ⊔ F) ∧ Function.Injective Θ ∧
    (∀ i j, Θ (smStarF i j) = Θ i * Θ j) ∧ (∀ i, Θ i ∈ E ↔ i.val < 64) ∧
    (∃ t₁ ∈ T, ∀ i, t₁ * Θ i * t₁⁻¹ = Θ (smTauF 1 0 i)) ∧
    (∃ t₂ ∈ T, ∀ i, t₂ * Θ i * t₂⁻¹ = Θ (smTauF 0 1 i)) ∧
    ∀ t ∈ T, ∃ a b : ℕ, ∀ i, t * Θ i * t⁻¹ = Θ (smTauF a b i) := by
  classical
  have hω : omegaP ∈ (T.subgroupOf (normalizer (E : Set G))).map hc.psi :=
    hTψ ▸ omegaP_mem_om9
  obtain ⟨n₁, hn₁, hn₁e⟩ := hω
  have hμ : muP ∈ (T.subgroupOf (normalizer (E : Set G))).map hc.psi := hTψ ▸ muP_mem_om9
  obtain ⟨n₂, hn₂, hn₂e⟩ := hμ
  have ht₁T : (n₁ : G) ∈ T := hn₁
  have ht₂T : (n₂ : G) ∈ T := hn₂
  have ht₁ : hc.psi ⟨n₁, kPrime_le_normalizer hc (hTK ht₁T)⟩ = omegaP := hn₁e
  have ht₂ : hc.psi ⟨n₂, kPrime_le_normalizer hc (hTK ht₂T)⟩ = muP := hn₂e
  have ht₁F : (n₁ : G) ∈ normalizer (F : Set G) :=
    hD.mem_normalizer_F (kPrime_le_normalizer_sup hc15 hS h44 hD hc hRg (hTK ht₁T)) n₁.2
  have hex := fun m (hm : m < 4) => exists_mem_F_comm hc15 hS h44 hD hc hRg n₁.2 hn₁e ht₁F hm
  let f₀ : ℕ → G := fun m => if hm : m < 4 then Classical.choose (hex m hm) else 1
  have hf₀ : ∀ m (hm : m < 4), f₀ m = Classical.choose (hex m hm) := fun m hm => by
    simp only [f₀, hm, ↓reduceDIte]
  have hf₀F : ∀ m < 4, f₀ m ∈ F := fun m hm => by
    obtain ⟨hF, -, -⟩ := Classical.choose_spec (hex m hm)
    rw [hf₀ m hm]
    exact hF
  have hf₀t : ∀ m < 4, (n₁ : G) * f₀ m = f₀ m * n₁ := fun m hm => by
    obtain ⟨-, ht, -⟩ := Classical.choose_spec (hex m hm)
    rw [hf₀ m hm]
    exact ht
  have hf₀ψ : ∀ m (hm : m < 4), hc.psi ⟨f₀ m, hD.F_le_normalizer (hf₀F m hm)⟩ = v0P m := by
    intro m hm
    obtain ⟨hF, -, hψ⟩ := Classical.choose_spec (hex m hm)
    have e : (⟨f₀ m, hD.F_le_normalizer (hf₀F m hm)⟩ : ↥(normalizer (E : Set G))) =
        ⟨Classical.choose (hex m hm), hD.F_le_normalizer hF⟩ := Subtype.ext (hf₀ m hm)
    rw [e, hψ]
  have htau := fun {t : G} (htT : t ∈ T) {a b : ℕ} (ha : a < 3) (hb : b < 3)
      (ht : hc.psi ⟨t, kPrime_le_normalizer hc (hTK htT)⟩ = omegaP ^ a * muP ^ b) =>
    thetaS_tau hc15 hS h44 hD hc hRg hTK hT3 hTψ ht₁T ht₁ hf₀F hf₀t hf₀ψ htT ha hb ht
  refine ⟨thetaS rep f₀, thetaS_mem hc hf₀F,
    thetaS_injective hc15 h44 hD hc hTK ht₁T ht₁ hf₀F hf₀t hf₀ψ,
    thetaS_mul hc15 h44 hD hc hTK ht₁T ht₁ hf₀F hf₀t hf₀ψ,
    thetaS_mem_E_iff hc15 h44 hD hc hTK ht₁T ht₁ hf₀F hf₀t hf₀ψ,
    ⟨n₁, ht₁T, htau ht₁T (by norm_num) (by norm_num) (by rw [ht₁, pow_one, pow_zero, mul_one])⟩,
    ⟨n₂, ht₂T, htau ht₂T (by norm_num) (by norm_num) (by rw [ht₂, pow_one, pow_zero, one_mul])⟩,
    fun t htT => ?_⟩
  obtain ⟨a, b, hab⟩ := exists_eq_of_mem_om9 hc15 h44 (psi_mem_om9_of_mem hc hTK hTψ htT)
  have hmod : ∀ (x : Equiv.Perm (Fin 64)), x ^ 3 = 1 → ∀ k : ℕ, x ^ k = x ^ (k % 3) := by
    intro x hx k
    conv_lhs => rw [← Nat.mod_add_div k 3, pow_add, pow_mul, hx, one_pow, mul_one]
  refine ⟨a % 3, b % 3, htau htT (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) ?_⟩
  rw [hab, ← hmod _ (omegaP_pow_three hc15 h44), ← hmod _ (muP_pow_three hc15 h44)]

end TData

end Theta

end CFSG.ComponentClassification.AS81
