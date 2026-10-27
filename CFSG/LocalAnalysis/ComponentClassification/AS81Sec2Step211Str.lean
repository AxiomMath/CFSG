module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211Cent
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard Hexa
open scoped commutatorElement


variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_sec2K {E : Subgroup G} {n k : G} (hn : n ∈ normalizer (sec2P E : Set G))
    (hk : k ∈ sec2K E) : n * k * n⁻¹ ∈ sec2K E := by
  have hle : sec2K E ≤ (sec2K E).comap (MulAut.conj n).toMonoidHom := by
    change closure {x | x ∈ normalizer (sec2P E : Set G) ∧ Odd (orderOf x)} ≤ _
    refine (closure_le _).mpr fun y hy => ?_
    obtain ⟨hyN, hyo⟩ := hy
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom]
    refine subset_closure ⟨?_, by rwa [MulEquiv.orderOf_eq]⟩
    rw [MulAut.conj_apply]
    exact mul_mem (mul_mem hn hyN) (inv_mem hn)
  exact hle hk

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)
  (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F))) (e : ↥(sec2PlanesP E F) ≃ Fin 6)
  {rep : Fin 64 → G} {ψ : ↥(normalizer (sec2P E : Set G)) →* Equiv.Perm (Fin 64)}
  (hc : Sec2HexaCoord E A F rep e ψ)

include h11 hE16 hF hL hodd hx hxS h4 hc

theorem exists_sec2K_shift_diag : ∃ a b : ↥(normalizer (sec2P E : Set G)),
    (a : G) ∈ sec2K E ∧ (b : G) ∈ sec2K E ∧
    sec2PlanesActionFin E F e a = Equiv.swap 0 2 * Equiv.swap 0 1 ∧
    sec2PlanesActionFin E F e b = Equiv.swap 3 5 * Equiv.swap 3 4 ∧
    (∃ i : Fin 3, ∀ v, ψ a v = shiftF (scalF i v)) ∧
    (∃ j : Fin 3, ∀ v, ψ b v = diagF (scalF j v)) := by
  obtain ⟨a, ha, haσ⟩ := exists_mem_sec2K_eq_of_mem_alternatingGroup h11 hE16 hF hL hodd hx hxS
    h4 e (σ := Equiv.swap 0 2 * Equiv.swap 0 1)
    (by rw [Equiv.Perm.mem_alternatingGroup]; simp [Equiv.Perm.sign_mul])
  obtain ⟨b, hb, hbσ⟩ := exists_mem_sec2K_eq_of_mem_alternatingGroup h11 hE16 hF hL hodd hx hxS
    h4 e (σ := Equiv.swap 3 5 * Equiv.swap 3 4)
    (by rw [Equiv.Perm.mem_alternatingGroup]; simp [Equiv.Perm.sign_mul])
  have hova := psi_mem_oval h11 hE16 hF hL hodd hc a
  have hovb := psi_mem_oval h11 hE16 hF hL hodd hc b
  rw [haσ] at hova
  rw [hbσ] at hovb
  refine ⟨a, b, ha, hb, haσ, hbσ, exists_scalF_eq_shiftF (hc.psi_add a) fun v =>
    ⟨hova 0 v, hova 1 v, hova 2 v, hova 3 v, hova 4 v, hova 5 v⟩,
    exists_scalF_eq_diagF (hc.psi_add b) fun v =>
    ⟨hovb 0 v, hovb 1 v, hovb 2 v, hovb 3 v, hovb 4 v, hovb 5 v⟩⟩

theorem exists_sec2K_omega : ∃ n : ↥(normalizer (sec2P E : Set G)),
    (n : G) ∈ ⁅sec2K E, sec2K E⁆ ∧ sec2PlanesActionFin E F e n = 1 ∧
    (ψ n = omegaPerm ∨ ψ n = omegaPerm * omegaPerm) := by
  obtain ⟨a, ha, haσ⟩ := exists_mem_sec2K_eq_of_mem_alternatingGroup h11 hE16 hF hL hodd hx hxS
    h4 e (σ := Equiv.swap 0 2 * Equiv.swap 0 1)
    (by rw [Equiv.Perm.mem_alternatingGroup]; simp [Equiv.Perm.sign_mul])
  obtain ⟨b, hb, hbσ⟩ := exists_mem_sec2K_eq_of_mem_alternatingGroup h11 hE16 hF hL hodd hx hxS
    h4 e (σ := Equiv.swap 3 5 * Equiv.swap 3 4)
    (by rw [Equiv.Perm.mem_alternatingGroup]; simp [Equiv.Perm.sign_mul])
  have hova := psi_mem_oval h11 hE16 hF hL hodd hc a
  have hovb := psi_mem_oval h11 hE16 hF hL hodd hc b
  rw [haσ] at hova
  rw [hbσ] at hovb
  have hne := ne_of_ovals (hc.psi_add a) (hc.psi_add b)
    (fun v => ⟨hova 0 v, hova 1 v, hova 2 v, hova 3 v, hova 4 v, hova 5 v⟩)
    (fun v => ⟨hovb 0 v, hovb 1 v, hovb 2 v, hovb 3 v, hovb 4 v, hovb 5 v⟩)
  have hρ : sec2PlanesActionFin E F e (a * b * a⁻¹ * b⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, haσ, hbσ]
    decide
  refine ⟨a * b * a⁻¹ * b⁻¹, Subgroup.commutator_mem_commutator ha hb, hρ, ?_⟩
  rcases psi_eq_of_mem_ker h11 hE16 hF hL hodd hc _ hρ with h | h | h
  · exfalso
    apply hne
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h
    calc ψ a * ψ b = ψ a * ψ b * (ψ a)⁻¹ * (ψ b)⁻¹ * (ψ b * ψ a) := by group
      _ = ψ b * ψ a := by rw [h, one_mul]
  · exact Or.inl h
  · exact Or.inr h

theorem ker_sec2KAction : (sec2KAction E F e).ker =
    (sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G)).subgroupOf (sec2K E) := by
  ext k
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h
    exact Subgroup.mem_inf.mpr ⟨k.2,
      mem_centralizer_of_sec2KAction_eq_one h11 hE16 hF hL hodd hx hxS h4 e hc h⟩
  · intro h
    exact sec2KAction_eq_one_of_mem_centralizer h11 hE16 hF hL hodd hx hxS h4 e hc
      (Subgroup.mem_inf.mp h).2

theorem eq_or_eq_of_le_sec2P {B : Subgroup G} (hEB : E ⊓ A ≤ B) (hBP : B ≤ sec2P E)
    (hKB : sec2K E ≤ normalizer (B : Set G)) : B = E ⊓ A ∨ B = sec2P E := by
  by_cases hBE : B ≤ E ⊓ A
  · exact Or.inl (le_antisymm hBE hEB)
  right
  obtain ⟨b, hbB, hbE⟩ := Set.not_subset.mp hBE
  have hxor : ∀ v w, rep v ∈ B → rep w ∈ B → rep (xorF v w) ∈ B := fun v w hv hw => by
    have h1 := hc.add v w
    have e1 : rep (xorF v w) = rep v * rep w * ((rep (xorF v w))⁻¹ * (rep v * rep w))⁻¹ := by
      group
    rw [e1]
    exact mul_mem (mul_mem hv hw) (inv_mem (hEB h1))
  have hψ : ∀ k : ↥(normalizer (sec2P E : Set G)), (k : G) ∈ sec2K E →
      ∀ v, rep v ∈ B → rep (ψ k v) ∈ B := fun k hk v hv => by
    have h1 := hc.conj k v
    have h2 : (k : G) * rep v * (k : G)⁻¹ ∈ B := (mem_normalizer_iff.mp (hKB hk) _).mp hv
    have e1 : rep (ψ k v) = (k : G) * rep v * (k : G)⁻¹ *
        ((rep (ψ k v))⁻¹ * ((k : G) * rep v * (k : G)⁻¹))⁻¹ := by group
    rw [e1]
    exact mul_mem h2 (inv_mem (hEB h1))
  obtain ⟨n, hnc, -, hnω⟩ := exists_sec2K_omega h11 hE16 hF hL hodd hx hxS h4 e hc
  have hnK : (n : G) ∈ sec2K E := Subgroup.commutator_le_self _ hnc
  have hω : ∀ v, rep v ∈ B → rep (omegaF v) ∈ B := fun v hv => by
    rcases hnω with h | h
    · have h1 := hψ n hnK v hv
      rwa [h, omegaPerm_apply] at h1
    · have h1 := hψ n hnK _ (hψ n hnK v hv)
      simp only [h, Equiv.Perm.mul_apply, omegaPerm_apply, omegaF_omegaF_omegaF] at h1
      exact h1
  have hscal : ∀ i : Fin 3, ∀ v, rep v ∈ B → rep (scalF i v) ∈ B := fun i v hv => by
    fin_cases i
    · exact hv
    · exact hω v hv
    · exact hω _ (hω v hv)
  obtain ⟨a, b', ha, hb', -, -, ⟨i, hi⟩, ⟨j, hj⟩⟩ :=
    exists_sec2K_shift_diag h11 hE16 hF hL hodd hx hxS h4 e hc
  have hS : ∀ v, rep v ∈ B → rep (shiftF v) ∈ B := fun v hv => by
    obtain ⟨i', hi'⟩ := exists_scalF_scalF_eq i
    have h1 := hψ a ha _ (hscal i' v hv)
    rwa [hi, hi'] at h1
  have hD : ∀ v, rep v ∈ B → rep (diagF v) ∈ B := fun v hv => by
    obtain ⟨j', hj'⟩ := exists_scalF_scalF_eq j
    have h1 := hψ b' hb' _ (hscal j' v hv)
    rwa [hj, hj'] at h1
  obtain ⟨v, hv⟩ := hc.surj b (hBP hbB)
  have hpv : rep v ∈ B := by
    have e1 : rep v = b * (b⁻¹ * rep v) := by group
    rw [e1]
    exact mul_mem hbB (hEB hv)
  have hv0 : v ≠ 0 := fun h => hbE (by
    rw [h] at hv
    have h0 : rep 0 ∈ E ⊓ A := by
      have h1 := hc.add 0 0
      rw [show xorF 0 0 = 0 by decide] at h1
      simpa using h1
    have e1 : b = rep 0 * (b⁻¹ * rep 0)⁻¹ := by group
    rw [e1]
    exact mul_mem h0 (inv_mem hv))
  have hall := forall_of_closed (fun v => rep v ∈ B) hxor hω hS hD hv0 hpv
  refine le_antisymm hBP fun q hq => ?_
  obtain ⟨w, hw⟩ := hc.surj q hq
  have e1 : q = rep w * (q⁻¹ * rep w)⁻¹ := by group
  rw [e1]
  exact mul_mem (hall w) (inv_mem (hEB hw))

omit hc in
theorem inf_le_sec2K : E ⊓ A ≤ sec2K E := by
  obtain ⟨e⟩ := nonempty_equiv_fin h11 hE16 hF hL hodd hx hxS h4
  obtain ⟨a, ha, ⟨j, hj⟩, haP, hρ⟩ := exists_five_element h11 hE16 hF hL hodd hx hxS h4 e
  have hodd' : Odd (orderOf a) := by
    obtain ⟨i, -, hi⟩ :=
      (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp (orderOf_dvd_of_pow_eq_one hj)
    rw [hi]
    exact Odd.pow (by decide)
  have haK : a ∈ sec2K E := mem_sec2K_of_odd haP hodd'
  have hfix : ∀ w ∈ E ⊓ A, a * w * a⁻¹ = w → w = 1 := fun w hw h =>
    eq_one_of_conj_eq_of_five h11 hE16 hF hL hodd hx hxS e ha.1 hj haP hρ hw h
  let f : ↥(E ⊓ A) → ↥(E ⊓ A) := fun d =>
    ⟨(d : G)⁻¹ * (a * d * a⁻¹), mul_mem (inv_mem d.2) ((mem_normalizer_iff.mp ha.2 d).mp d.2)⟩
  have hinj : Function.Injective f := by
    intro d d' h
    have h1 : (d : G)⁻¹ * (a * d * a⁻¹) = (d' : G)⁻¹ * (a * d' * a⁻¹) := congrArg Subtype.val h
    have h2 : a * ((d : G) * (d' : G)⁻¹) * a⁻¹ = (d : G) * (d' : G)⁻¹ := by
      calc a * ((d : G) * (d' : G)⁻¹) * a⁻¹ = d * ((d : G)⁻¹ * (a * d * a⁻¹)) *
            ((d' : G)⁻¹ * (a * d' * a⁻¹))⁻¹ * (d' : G)⁻¹ := by group
        _ = (d : G) * (d' : G)⁻¹ := by rw [h1]; group
    have h3 := hfix _ (mul_mem d.2 (inv_mem d'.2)) h2
    exact Subtype.ext (mul_inv_eq_one.mp h3)
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro w hw
  obtain ⟨d, hd⟩ := hsurj ⟨w, hw⟩
  have hw' : w = (d : G)⁻¹ * (a * d * a⁻¹) := (congrArg Subtype.val hd).symm
  have hdP : (d : G)⁻¹ ∈ normalizer (sec2P E : Set G) :=
    le_normalizer (inv_mem ((inf_le_left.trans (le_sec2P_of_frame hF)) d.2))
  have h1 := conj_mem_sec2K hdP haK
  rw [hw', show (d : G)⁻¹ * (a * d * a⁻¹) = (d : G)⁻¹ * a * ((d : G)⁻¹)⁻¹ * a⁻¹ by group]
  exact mul_mem h1 (inv_mem haK)

theorem sec2P_le_sec2K : sec2P E ≤ sec2K E := by
  have hEK := inf_le_sec2K h11 hE16 hF hL hodd hx hxS h4
  have hEP : E ⊓ A ≤ sec2P E := inf_le_left.trans (le_sec2P_of_frame hF)
  have hKN : sec2K E ≤ normalizer ((sec2P E ⊓ sec2K E : Subgroup G) : Set G) := fun k hk =>
    Sec2.mem_normalizer_of_forall_conj_mem fun q hq => Subgroup.mem_inf.mpr
      ⟨(mem_normalizer_iff.mp (sec2K_le_normalizer_sec2P E hk) q).mp hq.1,
        mul_mem (mul_mem hk hq.2) (inv_mem hk)⟩
  rcases eq_or_eq_of_le_sec2P h11 hE16 hF hL hodd hx hxS h4 e hc (le_inf hEP hEK) inf_le_left
    hKN with h | h
  · exfalso
    obtain ⟨n, hnc, -, hnω⟩ := exists_sec2K_omega h11 hE16 hF hL hodd hx hxS h4 e hc
    have hnK : (n : G) ∈ sec2K E := Subgroup.commutator_le_self _ hnc
    have hψ1 : ψ n = 1 := (psi_eq_one_iff h11 hE16 hF hL hodd hx hxS h4 hc n).mpr fun q hq => by
      have hqN : q⁻¹ ∈ normalizer (sec2P E : Set G) := le_normalizer (inv_mem hq)
      have h1 : q⁻¹ * ((n : G) * q * (n : G)⁻¹) ∈ sec2P E ⊓ sec2K E := by
        refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hq)
          ((mem_normalizer_iff.mp n.2 q).mp hq), ?_⟩
        rw [show q⁻¹ * ((n : G) * q * (n : G)⁻¹) = q⁻¹ * n * q⁻¹⁻¹ * (n : G)⁻¹ by group]
        exact mul_mem (conj_mem_sec2K hqN hnK) (inv_mem hnK)
      rw [h] at h1
      exact h1
    rcases hnω with h' | h'
    · exact omegaPerm_ne_one (h'.symm.trans hψ1)
    · exact omegaPerm_mul_omegaPerm_ne_one (h'.symm.trans hψ1)
  · intro q hq
    rw [← h] at hq
    exact hq.2

theorem centralizerMod_eq_sup :
    centralizerMod (sec2K E) (sec2P E) (E ⊓ A) = sec2P E ⊔ AS76b.oddCoreIn (sec2K E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPK := sec2P_le_sec2K h11 hE16 hF hL hodd hx hxS h4 e hc
  have hCC := centralizerMod_le_centralizer h11 hE16 hF hL hodd hx hxS h4
  have hsyl := isSylowOf_sec2P_centralizer h11 hE16 hF hL hodd hx hxS h4
  have hNP := normalizer_sec2P_le_normalizer_inf h11 hE16 hF hL hodd hx hxS h4
  have hPC := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  have hP2 := Sec2.isPGroup_sec2P E
  have hKP := sec2K_le_normalizer_sec2P E
  have hEP : E ⊓ A ≤ sec2P E := inf_le_left.trans (le_sec2P_of_frame hF)
  apply le_antisymm
  · intro c hc
    obtain ⟨y, hy, hy2, w, hw, hwo, rfl⟩ := exists_two_mul_odd c
    have hyC := (zpowers_le.mpr hc) hy
    have hwC := (zpowers_le.mpr hc) hw
    have hyP : y ∈ sec2P E := by
      have hQ : IsPGroup 2 ↥(sec2P E ⊔ zpowers y) := hP2.to_sup_of_normal_left' hy2
        (zpowers_le.mpr (hKP (mem_centralizerMod.mp hyC).1))
      have heq := hsyl.eq_of_le le_sup_left (sup_le hsyl.le (zpowers_le.mpr (hCC hyC))) hQ
      rw [← heq]
      exact mem_sup_right (mem_zpowers y)
    obtain ⟨hwK, -, hwP⟩ := mem_centralizerMod.mp hwC
    have hwE := hCC hwC
    have hw2 : w ^ 2 ∈ centralizer (sec2P E : Set G) := mem_centralizer_iff.mpr fun q hq => by
      set d := q⁻¹ * w⁻¹ * q * w with hd
      have hdE : d ∈ E ⊓ A := hwP q hq
      have h1 : w⁻¹ * q * w = q * d := by rw [hd]; group
      have h2 : w⁻¹ * d * w = d := by
        calc w⁻¹ * d * w = w⁻¹ * (d * w) := by group
          _ = w⁻¹ * (w * d) := by rw [mem_centralizer_iff.mp hwE d hdE]
          _ = d := by group
      have h3 : d * d = 1 := by
        obtain ⟨hEe, -⟩ := isElemAbelian_and_card_of_mem_planes hF
          (⟨1, Or.inl (rightConjugate_one E).symm⟩ : E ∈ planes E F)
        rw [← sq]
        exact hEe.2 d hdE.1
      have h4' : (w ^ 2)⁻¹ * q * w ^ 2 = q := by
        calc (w ^ 2)⁻¹ * q * w ^ 2 = w⁻¹ * (w⁻¹ * q * w) * w := by rw [sq]; group
          _ = w⁻¹ * (q * d) * w := by rw [h1]
          _ = (w⁻¹ * q * w) * (w⁻¹ * d * w) := by group
          _ = q * d * d := by rw [h1, h2]
          _ = q := by rw [mul_assoc, h3, mul_one]
      calc q * w ^ 2 = w ^ 2 * ((w ^ 2)⁻¹ * q * w ^ 2) := by group
        _ = w ^ 2 * q := by rw [h4']
    have hwCP : w ∈ centralizer (sec2P E : Set G) := by
      obtain ⟨m, hm⟩ := hwo
      have e1 : w = (w ^ 2) ^ (m + 1) := by
        rw [← pow_mul, show 2 * (m + 1) = orderOf w + 1 by omega, pow_succ, pow_orderOf_eq_one,
          one_mul]
      rw [e1]
      exact pow_mem hw2 _
    set D := sec2K E ⊓ centralizer (sec2P E : Set G) with hD
    have hDK : D ≤ sec2K E := inf_le_left
    have hDN : sec2K E ≤ normalizer (D : Set G) := fun k hk =>
      Sec2.mem_normalizer_of_forall_conj_mem fun z hz => Subgroup.mem_inf.mpr
        ⟨mul_mem (mul_mem hk hz.1) (inv_mem hk), mem_centralizer_iff.mpr fun q hq => by
          have hq' : k⁻¹ * q * k⁻¹⁻¹ ∈ sec2P E :=
            (mem_normalizer_iff.mp (inv_mem (hKP hk)) q).mp hq
          have h1 := mem_centralizer_iff.mp hz.2 _ hq'
          calc q * (k * z * k⁻¹) = k * ((k⁻¹ * q * k⁻¹⁻¹) * z) * k⁻¹ := by group
            _ = k * (z * (k⁻¹ * q * k⁻¹⁻¹)) * k⁻¹ := by rw [h1]
            _ = k * z * k⁻¹ * q := by group⟩
    have hsylD : IsSylowOf 2 (sec2P E ⊓ D) D := by
      have hPX : sec2P E ≤ sec2P E ⊔ D := le_sup_left
      have hXC : sec2P E ⊔ D ≤ centralizer ((E ⊓ A : Subgroup G) : Set G) :=
        sup_le hsyl.le (inf_le_right.trans (centralizer_le hEP))
      have hsylX : IsSylowOf 2 (sec2P E) (sec2P E ⊔ D) := by
        rw [isSylowOf_iff] at hsyl ⊢
        refine ⟨hPX, hP2, fun h2 => hsyl.2.2 ?_⟩
        rw [← relIndex_mul_relIndex _ _ _ hPX hXC]
        exact dvd_mul_of_dvd_left h2 _
      exact hsylX.inf_of_le_normalizer le_sup_right
        (sup_le (fun q hq => hDN (hPK hq)) le_normalizer)
    have hDeq := eq_sup_oddCoreIn_of_central hsylD.isPGroup inf_le_right
      (fun z hz => mem_centralizer_iff.mpr fun d hd =>
        (mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 z hz.1).symm)
      (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp ((isSylowOf_iff.mp hsylD).2.2)))
    have hOD : AS76b.oddCoreIn D ≤ AS76b.oddCoreIn (sec2K E) := by
      have hOK := (AS76b.oddCoreIn_le D).trans hDK
      have hn : ((AS76b.oddCoreIn D).subgroupOf (sec2K E)).Normal :=
        (normal_subgroupOf_iff_le_normalizer hOK).mpr
          (hDN.trans (AS76b.normalizer_le_normalizer_oddCoreIn D))
      have hodd' : Odd (Nat.card ((AS76b.oddCoreIn D).subgroupOf (sec2K E))) := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hOK).toEquiv]
        exact AS76b.odd_card_oddCoreIn D
      have h := AS76b.le_assemblyOddCore hn hodd'
      intro z hz
      exact ⟨⟨z, hOK hz⟩, h (show (⟨z, hOK hz⟩ : ↥(sec2K E)) ∈ _ from hz), rfl⟩
    have hwD : w ∈ D := Subgroup.mem_inf.mpr ⟨hwK, hwCP⟩
    rw [hDeq] at hwD
    exact mul_mem (mem_sup_left hyP) (sup_le_sup (inf_le_left) hOD hwD)
  · refine sup_le (fun q hq => ?_) (fun o ho => ?_)
    · refine mem_centralizerMod.mpr ⟨hPK hq, hNP (le_normalizer hq), fun p hp => ?_⟩
      have h1 := (sq_mem_and_commutator_mem_inf h11 hE16 hF hL hodd hx hxS h4 (inv_mem hp)
        (inv_mem hq)).2
      simpa using h1
    · have hoK := AS76b.oddCoreIn_le (sec2K E) ho
      refine mem_centralizerMod.mpr ⟨hoK, hNP (hKP hoK), fun p hp => ?_⟩
      have h1 : p⁻¹ * o⁻¹ * p * o ∈ AS76b.oddCoreIn (sec2K E) ⊓ sec2P E := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have h2 : p⁻¹ * o⁻¹ * p⁻¹⁻¹ ∈ AS76b.oddCoreIn (sec2K E) :=
            (mem_normalizer_iff.mp (AS76b.le_normalizer_oddCoreIn (sec2K E)
              (inv_mem (hPK hp))) _).mp (inv_mem ho)
          rw [inv_inv] at h2
          exact mul_mem h2 ho
        · have h2 : o⁻¹ * p * o⁻¹⁻¹ ∈ sec2P E :=
            (mem_normalizer_iff.mp (inv_mem (hKP hoK)) p).mp hp
          rw [inv_inv] at h2
          rw [show p⁻¹ * o⁻¹ * p * o = p⁻¹ * (o⁻¹ * p * o) by group]
          exact mul_mem (inv_mem hp) h2
      rw [AS76b.oddCoreIn_inf_eq_bot hP2, mem_bot] at h1
      rw [h1]
      exact one_mem _

theorem relIndex_centralizerMod :
    (centralizerMod (sec2K E) (sec2P E) (E ⊓ A)).relIndex (sec2K E) = 1080 := by
  set C := centralizerMod (sec2K E) (sec2P E) (E ⊓ A) with hC
  set K₆ := sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G) with hK₆
  have hKP := sec2K_le_normalizer_sec2P E
  have hCK₆ : C ≤ K₆ := fun c hc => Subgroup.mem_inf.mpr ⟨(mem_centralizerMod.mp hc).1,
    centralizerMod_le_centralizer h11 hE16 hF hL hodd hx hxS h4 hc⟩
  have hK₆K : K₆ ≤ sec2K E := inf_le_left
  have h360 : K₆.relIndex (sec2K E) = 360 := by
    rw [Subgroup.relIndex, ← ker_sec2KAction h11 hE16 hF hL hodd hx hxS h4 e hc,
      Subgroup.index_ker, MonoidHom.range_eq_top.mpr
        (sec2KAction_surjective h11 hE16 hF hL hodd hx hxS h4 e), card_top,
      nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  set ψ₆ : ↥K₆ →* Equiv.Perm (Fin 64) := ψ.comp (inclusion (hK₆K.trans hKP)) with hψ₆
  have hker : ψ₆.ker = C.subgroupOf K₆ := by
    ext k
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact (mem_centralizerMod_iff_psi h11 hE16 hF hL hodd hx hxS h4 e hc
      (n := inclusion (hK₆K.trans hKP) k) (Subgroup.mem_inf.mp k.2).1).symm
  have hrange : ψ₆.range = zpowers omegaPerm := by
    apply le_antisymm
    · rintro _ ⟨k, rfl⟩
      have hk1 := sec2KAction_eq_one_of_mem_centralizer h11 hE16 hF hL hodd hx hxS h4 e hc
        (k := ⟨k, (Subgroup.mem_inf.mp k.2).1⟩) (Subgroup.mem_inf.mp k.2).2
      have hρ : sec2PlanesActionFin E F e (inclusion (hK₆K.trans hKP) k) = 1 :=
        congrArg Subtype.val hk1
      rcases psi_eq_of_mem_ker h11 hE16 hF hL hodd hc _ hρ with h | h | h
      · rw [hψ₆, MonoidHom.comp_apply, h]
        exact one_mem _
      · rw [hψ₆, MonoidHom.comp_apply, h]
        exact mem_zpowers _
      · rw [hψ₆, MonoidHom.comp_apply, h]
        exact mul_mem (mem_zpowers _) (mem_zpowers _)
    · rw [zpowers_le]
      obtain ⟨n, hnc, hρn, hnω⟩ := exists_sec2K_omega h11 hE16 hF hL hodd hx hxS h4 e hc
      have hnK : (n : G) ∈ sec2K E := Subgroup.commutator_le_self _ hnc
      have hnK₆ : (n : G) ∈ K₆ := Subgroup.mem_inf.mpr ⟨hnK,
        mem_centralizer_of_sec2KAction_eq_one h11 hE16 hF hL hodd hx hxS h4 e hc
          (t := ⟨n, hnK⟩) (Subtype.ext hρn)⟩
      have hψn : ψ₆ ⟨n, hnK₆⟩ = ψ n := rfl
      rcases hnω with h | h
      · exact ⟨⟨n, hnK₆⟩, by rw [hψn, h]⟩
      · exact ⟨⟨n, hnK₆⟩ ^ 2, by rw [map_pow, hψn, h, omegaPerm_mul_omegaPerm_sq]⟩
  have h3 : C.relIndex K₆ = 3 := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hrange, Nat.card_zpowers,
      orderOf_omegaPerm]
  rw [← relIndex_mul_relIndex C K₆ (sec2K E) hCK₆ hK₆K, h3, h360]

theorem commutator_sup_centralizerMod_eq :
    ⁅sec2K E, sec2K E⁆ ⊔ centralizerMod (sec2K E) (sec2P E) (E ⊓ A) = sec2K E := by
  have hKP := sec2K_le_normalizer_sec2P E
  refine le_antisymm (sup_le (Subgroup.commutator_le_self _)
    fun c hc => (mem_centralizerMod.mp hc).1) fun k hk => ?_
  set φ := sec2KAction E F e with hφ
  have hsurj := sec2KAction_surjective h11 hE16 hF hL hodd hx hxS h4 e
  have hcomm : (_root_.commutator ↥(sec2K E)).map φ = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr hsurj, ← _root_.commutator_def]
    exact commutator_alternatingGroup_eq_top
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  obtain ⟨c, hcc, hcφ⟩ : φ ⟨k, hk⟩ ∈ (_root_.commutator ↥(sec2K E)).map φ :=
    hcomm ▸ mem_top _
  have hcG : (c : G) ∈ ⁅sec2K E, sec2K E⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨c, hcc, rfl⟩
  set m : ↥(sec2K E) := c⁻¹ * ⟨k, hk⟩ with hm
  have hmφ : φ m = 1 := by rw [hm, map_mul, map_inv, hcφ, inv_mul_cancel]
  have hmρ : sec2PlanesActionFin E F e ⟨m, hKP m.2⟩ = 1 := congrArg Subtype.val hmφ
  obtain ⟨n, hnc, -, hnω⟩ := exists_sec2K_omega h11 hE16 hF hL hodd hx hxS h4 e hc
  have hnK : (n : G) ∈ sec2K E := Subgroup.commutator_le_self _ hnc
  have hpow : ∃ i : ℕ, ψ ⟨m, hKP m.2⟩ = ψ n ^ i := by
    rcases psi_eq_of_mem_ker h11 hE16 hF hL hodd hc _ hmρ with h | h | h <;>
      rcases hnω with h' | h'
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, h', pow_one]⟩
    · exact ⟨2, by rw [h, h', omegaPerm_mul_omegaPerm_sq]⟩
    · exact ⟨2, by rw [h, h', sq]⟩
    · exact ⟨1, by rw [h, h', pow_one]⟩
  obtain ⟨i, hi⟩ := hpow
  have hrest : ((n ^ i)⁻¹ * ⟨m, hKP m.2⟩ : ↥(normalizer (sec2P E : Set G))) ∈
      ((centralizerMod (sec2K E) (sec2P E) (E ⊓ A)).subgroupOf
        (normalizer (sec2P E : Set G))) := by
    rw [mem_subgroupOf]
    refine (mem_centralizerMod_iff_psi h11 hE16 hF hL hodd hx hxS h4 e hc ?_).mpr ?_
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      exact mul_mem (inv_mem (pow_mem hnK i)) m.2
    · rw [map_mul, map_inv, map_pow, hi, inv_mul_cancel]
  rw [mem_subgroupOf] at hrest
  have e1 : k = (c : G) * ((n : G) ^ i * (((n ^ i)⁻¹ * ⟨m, hKP m.2⟩ :
      ↥(normalizer (sec2P E : Set G))) : G)) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hm]
    group
  rw [e1]
  exact mul_mem (mem_sup_left hcG) (mul_mem (mem_sup_left (pow_mem hnc i)) (mem_sup_right hrest))

end Frame

end CFSG.ComponentClassification.AS81
