module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightStrong
public import CFSG.Quasithin.Background.A1cTransferVariants

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]
variable {G T S Q H : Subgroup X} {g y : X}

namespace ElemCtx

theorem omegaOne_eq (c : ElemCtx G T S Q H g y) (hin : Theorem48Inputs) {u : X}
    (hu : u ∈ S ⊓ G) (hu2 : u ^ 2 = 1) : u ∈ (T ⊔ rightConjugate T g) ⊓ G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := c.elem
  by_cases huW : u ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)
  · exact mem_Z_of_sq e huW hu.2 hu2
  exfalso
  have hu1 : u ≠ 1 := fun h => huW (h ▸ Subgroup.one_mem _)
  have hord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  by_cases hfus : ∃ x ∈ G, x⁻¹ * u * x ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G
  · obtain ⟨x, hx, hxR⟩ := hfus
    have hxZ : x⁻¹ * u * x ∈ (T ⊔ rightConjugate T g) ⊓ G := by
      refine mem_Z_of_sq e hxR.1 hxR.2 ?_
      have h1 : (x⁻¹ * u * x) ^ 2 = x⁻¹ * u ^ 2 * x := by rw [pow_two, pow_two]; group
      rw [h1, hu2]
      group
    have h1 := c.stronglyClosed_Z hin _ hxZ x⁻¹ (G.inv_mem hx)
    have h2 : x⁻¹⁻¹ * (x⁻¹ * u * x) * x⁻¹ = u := by group
    rw [h2] at h1
    exact huW (Subgroup.mem_sup_right (h1 hu).1)
  · simp only [not_exists, not_and] at hfus
    obtain ⟨-, -, hodd⟩ := isSylowOf_iff.mp c.isSylowOf_P
    obtain ⟨N, hNG, -, hsq, huN⟩ := CFSG.Quasithin.thompson_transfer_exists_normal_subgroup
      (inf_le_right : S ⊓ G ≤ G) c.isSylowOf_P.isPGroup hodd
      (inf_le_inf_right G e.A_le_S) c.relIndex_R_P hu.2 hord hfus
    have heq := eq_of_sq_mem c.frame.isPGroup c.frame.le_normalizer c.commutator_eq hNG hsq
    exact huN (heq ▸ hu.2)

theorem comm_mem_Z_of_mem_P (c : ElemCtx G T S Q H g y) {a b : X} (ha : a ∈ S ⊓ G)
    (hb : b ∈ S ⊓ G) : a⁻¹ * (b⁻¹ * a * b) ∈ (T ⊔ rightConjugate T g) ⊓ G := by
  have e := c.elem
  by_cases haW : a ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)
  · exact c.comm_mem_Z_of_mem_S ⟨haW, ha.2⟩ hb.1
  by_cases hbW : b ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)
  · have h1 := c.comm_mem_Z_of_mem_S ⟨hbW, hb.2⟩ ha.1
    have h2 : a⁻¹ * (b⁻¹ * a * b) = (b⁻¹ * (a⁻¹ * b * a))⁻¹ := by group
    rw [h2]
    exact Subgroup.inv_mem _ h1
  · have hr : b * a⁻¹ ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G :=
      ⟨mul_inv_mem_W e ha.1 hb.1 haW hbW, G.mul_mem hb.2 (G.inv_mem ha.2)⟩
    have h1 := c.comm_mem_Z_of_mem_S hr ha.1
    have h2 := conj_mem_Z e ha.1 (Subgroup.inv_mem _ h1)
    have h3 : a⁻¹ * (b⁻¹ * a * b) = a⁻¹ * ((b * a⁻¹)⁻¹ * (a⁻¹ * (b * a⁻¹) * a))⁻¹ * a := by
      group
    rw [h3]
    exact h2

theorem false_of_stronglyClosed_R (c : ElemCtx G T S Q H g y)
    (hR : ∀ r ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G, ∀ x ∈ G,
      x⁻¹ * r * x ∈ S ⊓ G → x⁻¹ * r * x ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := c.elem
  have h := c.sylowFrame
  have hF := c.frame
  have hSW := S_le_normalizer_W e
  have hcoset : ∀ x ∈ S, ∀ x' ∈ S, x ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) →
      x' ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) →
      x⁻¹ * x' ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
    intro x hx x' hx' hxW hx'W
    have hxi : x⁻¹ ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) :=
      fun h => hxW (by simpa using Subgroup.inv_mem _ h)
    have hx'i : x'⁻¹ ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) :=
      fun h => hx'W (by simpa using Subgroup.inv_mem _ h)
    have h1 := mul_inv_mem_W e (S.inv_mem hx) (S.inv_mem hx') hxi hx'i
    have h2 := Subgroup.inv_mem _ h1
    simpa using h2
  obtain ⟨u, hu, huW⟩ := c.exists_not_mem_W
  obtain ⟨-, -, hidx⟩ := isSylowOf_iff.mp h.sylow
  have hindex : Nat.Coprime 2 (S.relIndex (G ⊔ T)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hidx
  have hKn : ∀ s ∈ S, ∀ k ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g),
      s * k * s⁻¹ ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) :=
    fun s hs k hk => (Subgroup.mem_normalizer_iff.mp (hSW hs) k).mp hk
  have habel : ⁅S, S⁆ ≤ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    by_cases haW : a ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)
    · have h1 := hKn b hb a⁻¹ (Subgroup.inv_mem _ haW)
      have h2 := Subgroup.mul_mem _ haW h1
      simpa [mul_assoc] using h2
    by_cases hbW : b ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)
    · exact Subgroup.mul_mem _ (hKn a ha b hbW) (Subgroup.inv_mem _ hbW)
    · have haW' : a⁻¹ ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) :=
        fun h => haW (by simpa using Subgroup.inv_mem _ h)
      have hbW' : b⁻¹ ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) :=
        fun h => hbW (by simpa using Subgroup.inv_mem _ h)
      have h1 := hcoset a⁻¹ (S.inv_mem ha) b hb haW' hbW
      have h2 := hcoset b⁻¹ (S.inv_mem hb) a ha hbW' haW
      have h4 : a * b * a⁻¹ * b⁻¹ = (a⁻¹⁻¹ * b) * (b⁻¹⁻¹ * a)⁻¹ := by group
      rw [h4]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
  obtain ⟨n, hn⟩ := h.sylow.isPGroup ⟨u, hu.1⟩
  have hgp : ∃ n : ℕ, u ^ 2 ^ n = 1 := ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hfus : ∀ (m : ℤ) (a : X), a ∈ G ⊔ T → a⁻¹ * u ^ m * a ∈ S →
      (u ^ m)⁻¹ * (a⁻¹ * u ^ m * a) ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
    intro m a ha haS
    obtain ⟨t, ht, k, hk, rfl⟩ := hF.mem_sup_iff.mp ha
    have humP : u ^ m ∈ S ⊓ G := Subgroup.zpow_mem _ hu m
    have htS := h.le ht
    have hvS : t⁻¹ * u ^ m * t ∈ S := by
      have := S.mul_mem (S.mul_mem (S.inv_mem htS) humP.1) htS
      simpa [mul_assoc] using this
    have hvG : t⁻¹ * u ^ m * t ∈ G := by
      have := (Subgroup.mem_normalizer_iff.mp (hF.le_normalizer (T.inv_mem ht)) _).mp humP.2
      simpa using this
    have hvW : t⁻¹ * u ^ m * t ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ↔
        u ^ m ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
      have := Subgroup.mem_normalizer_iff.mp (hSW (S.inv_mem htS)) (u ^ m)
      simpa using this.symm
    have heq : (t * k)⁻¹ * u ^ m * (t * k) = k⁻¹ * (t⁻¹ * u ^ m * t) * k := by group
    rw [heq] at haS ⊢
    have hkP : k⁻¹ * (t⁻¹ * u ^ m * t) * k ∈ S ⊓ G :=
      ⟨haS, G.mul_mem (G.mul_mem (G.inv_mem hk) hvG) hk⟩
    by_cases hmW : u ^ m ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)
    · have h1 := hR _ ⟨hvW.mpr hmW, hvG⟩ k hk hkP
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hmW) h1.1
    · have hkW : k⁻¹ * (t⁻¹ * u ^ m * t) * k ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
        intro hW
        have h1 := hR _ ⟨hW, hkP.2⟩ k⁻¹ (G.inv_mem hk)
        have h2 : k⁻¹⁻¹ * (k⁻¹ * (t⁻¹ * u ^ m * t) * k) * k⁻¹ = t⁻¹ * u ^ m * t := by group
        rw [h2] at h1
        exact hmW (hvW.mp (h1 ⟨hvS, hvG⟩).1)
      exact hcoset _ humP.1 _ haS hmW hkW
  have hnot := CFSG.Quasithin.generalized_thompson_transfer_one_subgroup h.sylow.le hindex
    e.A_le_S hKn habel hu.1 huW hgp hfus
  apply hnot
  have h1 : ⁅T, G⁆ ≤ ⁅G ⊔ T, G ⊔ T⁆ := Subgroup.commutator_mono le_sup_right le_sup_left
  rw [c.commutator_eq] at h1
  exact h1 hu.2

theorem false_of_comm_le (c : ElemCtx G T S Q H g y) {N : Subgroup X}
    (hNR : N ≤ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G)
    (hN : G ≤ Subgroup.normalizer (N : Set X))
    (hcomm : ∀ a ∈ S ⊓ G, ∀ b ∈ S ⊓ G, a⁻¹ * (b⁻¹ * a * b) ∈ N) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := c.elem
  have hP := c.isSylowOf_P
  have hPR := c.normalizer_P_le_R
  apply c.false_of_stronglyClosed_R
  intro r hr x hx hxP
  have hrP : r ∈ S ⊓ G := ⟨e.A_le_S hr.1, hr.2⟩
  set p := x⁻¹ * r * x with hpdef
  set C := commSub G N p hN with hCdef
  have hCG : C ≤ G := fun k hk => hk.1
  have hPC : S ⊓ G ≤ C := fun k hk => ⟨hk.2, hcomm k hk _ hxP⟩
  have hPxC : rightConjugate (S ⊓ G) x ≤ C := by
    intro k hk
    rw [mem_rightConjugate_iff] at hk
    have hkG : k ∈ G := by
      have := G.mul_mem (G.mul_mem (G.inv_mem hx) hk.2) hx
      simpa [mul_assoc] using this
    refine ⟨hkG, ?_⟩
    have h1 := hcomm _ hk r hrP
    have h2 := (Subgroup.mem_normalizer_iff.mp (hN (G.inv_mem hx)) _).mp h1
    have h3 : x⁻¹ * ((x * k * x⁻¹)⁻¹ * (r⁻¹ * (x * k * x⁻¹) * r)) * x⁻¹⁻¹ =
        k⁻¹ * (p⁻¹ * k * p) := by rw [hpdef]; group
    rwa [h3] at h2
  have hPC' : IsSylowOf 2 (S ⊓ G) C := hP.of_le hPC hCG
  have hPxC' : IsSylowOf 2 (rightConjugate (S ⊓ G) x) C :=
    (isSylowOf_rightConjugate hP hx).of_le hPxC hCG
  obtain ⟨k, hk, hkey⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hPC' hPxC'
  have hn : x * k ∈ G ⊓ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X) := by
    refine ⟨G.mul_mem hx hk.1, ?_⟩
    show x * k ∈ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X)
    rw [Subgroup.mem_normalizer_iff]
    intro v
    have h1 := hkey (k * v * k⁻¹)
    rw [mem_rightConjugate_iff] at h1
    have h2 : k⁻¹ * (k * v * k⁻¹) * k = v := by group
    have h3 : x * (k * v * k⁻¹) * x⁻¹ = x * k * v * (x * k)⁻¹ := by group
    rw [h2, h3] at h1
    exact h1.symm
  have hnR := hPR hn
  have hrn : (x * k)⁻¹ * r * (x * k) ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnR) r).mp hr
    simpa using this
  have h1 : p = ((x * k)⁻¹ * r * (x * k)) * (k⁻¹ * (p⁻¹ * k * p)) := by rw [hpdef]; group
  rw [h1]
  exact Subgroup.mul_mem _ hrn (hNR hk.2)

theorem false_of_normal_Z (c : ElemCtx G T S Q H g y)
    (hZ : G ≤ Subgroup.normalizer (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X)) :
    False :=
  c.false_of_comm_le (N := (T ⊔ rightConjugate T g) ⊓ G)
    (fun _ hz => ⟨Subgroup.mem_sup_right hz.1, hz.2⟩) hZ
    fun _ ha _ hb => c.comm_mem_Z_of_mem_P ha hb

end ElemCtx

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
