module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
public import CFSG.LieType.ChevTwo.OutData
import CFSG.LocalAnalysis.GLTheoremB.I2810.InducedAux
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.ThreeSubgroups

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.LieType.ChevTwo
open CFSG.HardMathSupport.Cooperstein.StructureLie (OutTwoRank InnAut)
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section Induced
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem c_card_indAut (h : Setup28 W K S) {B : Subgroup X} (hB : B ≤ S) :
    Nat.card ↥(indAut W K B) = (kerAct W K S).relIndex B := InducedAux.card_indAut h hB

theorem c_indAut_elemAbelian (h : Setup28 W K S) {A : Subgroup X} (hAS : A ≤ S)
    (hA : IsElemAbelian 2 A) : IsElemAbelian 2 (indAut W K A) :=
  ((hA.map (QuotientGroup.mk' W)).subgroupOf _).map _

private theorem card_le_four_of_outTwoRank {G : Type} [Group G] (hG : commutator G = ⊤)
    (hOut : OutTwoRank (G ⧸ Subgroup.center G)) {F : Subgroup (MulAut G)}
    (hF : F ⊓ (MulAut.conj : G →* MulAut G).range = ⊥) {E : Subgroup (MulAut G)} (hEF : E ≤ F)
    (hEa : IsElemAbelian 2 E) : Nat.card ↥E ≤ 4 := by
  have hinj : Function.Injective (InducedAux.autCenterQuot G) :=
    InducedAux.autCenterQuot_injective hG
  set P : Subgroup (MulAut (G ⧸ Subgroup.center G)) := E.map (InducedAux.autCenterQuot G) with hP
  have hPp : IsPGroup 2 ↥P := (hEa.map (InducedAux.autCenterQuot G)).isPGroup
  obtain ⟨_, hrank⟩ := hOut P hPp
  have hP2 : ∀ a ∈ P, a ^ 2 ∈ InnAut (G ⧸ Subgroup.center G) := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_pow, hEa.2 e he, map_one]
    exact Subgroup.one_mem _
  have hle := hrank P le_rfl hP2
  have hbot : P ⊓ InnAut (G ⧸ Subgroup.center G) = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨ha, hainn⟩
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hainn
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have heg : e = MulAut.conj g := by
      apply hinj
      rw [InducedAux.autCenterQuot_conj]
      exact hy.symm
    have hemem : e ∈ F ⊓ (MulAut.conj : G →* MulAut G).range := ⟨hEF he, ⟨g, heg.symm⟩⟩
    rw [hF, Subgroup.mem_bot] at hemem
    rw [hemem, map_one]
    exact Subgroup.one_mem _
  rw [hbot, Subgroup.relIndex_bot_left] at hle
  rwa [hP, Subgroup.card_map_of_injective hinj] at hle

theorem c_le_four_one (hOut : Chev2OutTwoRank) (h : Setup28 W K S) (h1 : Hyp28One W K S)
    {E : Subgroup (MulAut ↥(bar W K))} (hE : E ≤ indAut W K S) (hEa : IsElemAbelian 2 E) :
    Nat.card ↥E ≤ 4 := by
  obtain ⟨⟨hq, hchev⟩, _, hnoinn⟩ := h1
  exact card_le_four_of_outTwoRank hq.1.commutator_eq_top (hOut _ hq.2.1 hq.2.2 hchev) hnoinn hE hEa

theorem c_le_four_three (h : Setup28 W K S) (h3 : Hyp28Three W K S) :
    Nat.card ↥(indAut W K S) ≤ 4 := by
  obtain ⟨⟨hq, _⟩, _, n, e, V₄, V, hV₄, hVV₄, hact⟩ := h3
  have hT := InducedAux.card_le_of_induces hq.1.commutator_eq_top e (indAut W K S)
    (V.map (MulAut.conj : ↥(alternatingGroup (Fin n)) →* _)) hact.1
  have h1 : Nat.card ↥(V.map (MulAut.conj : ↥(alternatingGroup (Fin n)) →* _)) ≤ Nat.card ↥V :=
    Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective _ V)
  have h2 : Nat.card ↥V ≤ Nat.card ↥V₄ := Subgroup.card_le_of_le hVV₄
  have h4 : Nat.card ↥V₄ = 4 := hV₄.1
  omega

theorem transv_of_card_two (h : Setup28 W K S) (hR : Red28 W K S) {A : Subgroup X}
    (hA : Off28 W K S A) (hc : Nat.card ↥(indAut W K A) = 2) :
    ∃ a ∈ A, a ∉ kerAct W K S ∧ a ^ 2 = 1 ∧ TransvOn (vOf W K S) a := by
  have hAS : A ≤ S := hA.isMax.1
  have hAel : IsElemAbelian 2 A := hA.isMax.2.1
  have hrel : (kerAct W K S).relIndex A = 2 := by
    rw [← InducedAux.card_indAut h hAS]; exact hc
  obtain ⟨a, haA, hak⟩ := Set.not_subset.mp hA.not_le
  have hoff := hA.off
  rw [hrel] at hoff
  have haN : a ∈ K ⊔ S := Subgroup.mem_sup_right (hAS haA)
  have hnc : ¬ (∀ v ∈ vOf W K S, a * v = v * a) := fun hc' =>
    hak ⟨hAS haA, fun k hk => hR.cent_comm a haN hc' k hk⟩
  have hpos : (Subgroup.centralizer ({a} : Set X)).relIndex (vOf W K S) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hle : (Subgroup.centralizer ({a} : Set X)).relIndex (vOf W K S) ≤ 2 := by
    refine le_trans ?_ hoff
    refine Subgroup.relIndex_le_of_le_left (Subgroup.centralizer_le ?_) Subgroup.index_ne_zero_of_finite
    simpa using haA
  have hne1 : (Subgroup.centralizer ({a} : Set X)).relIndex (vOf W K S) ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    refine hnc fun v hv => ?_
    exact Subgroup.mem_centralizer_iff.mp (h1 hv) a (Set.mem_singleton a)
  have h2 : (Subgroup.centralizer ({a} : Set X)).relIndex (vOf W K S) = 2 := by omega
  obtain ⟨u, huV, hu1, hu⟩ := InducedAux.exists_transv_of_relIndex_two (vOf W K S)
    (fun v hv => hR.v_elem.2 v hv) a (fun v hv => hR.v_nrm a haN v hv) h2
  exact ⟨a, haA, hak, hAel.2 a haA, u, huV, hu1, hu⟩

end Induced

section Toolbox
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem odd_trivial_of_series {z : X} (hz : Odd (orderOf z)) {P Q : Subgroup X} (hP : IsPGroup 2 ↥P)
    (hQP : Q ≤ P) (hzP : ∀ x ∈ P, z * x * z⁻¹ ∈ P) (hzQ : ∀ q ∈ Q, z * q * z⁻¹ = q)
    (hzPQ : ∀ x ∈ P, ⁅z, x⁆ ∈ Q) : ∀ x ∈ P, z * x * z⁻¹ = x := by
  intro x hx
  set c : X := ⁅z, x⁆ with hc
  have hcQ : c ∈ Q := hzPQ x hx
  have h3 : z * x * z⁻¹ = c * x := by simp [hc, commutatorElement_def]
  have key : ∀ k : ℕ, z ^ k * x * (z ^ k)⁻¹ = c ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : z ^ (k + 1) * x * (z ^ (k + 1))⁻¹ = z * (z ^ k * x * (z ^ k)⁻¹) * z⁻¹ := by
        rw [pow_succ']; group
      rw [h1, ih]
      have h2 : z * (c ^ k * x) * z⁻¹ = (z * c * z⁻¹) ^ k * (z * x * z⁻¹) := by
        rw [conj_pow]; group
      rw [h2, hzQ c hcQ, h3, pow_succ]
      group
  have h1 : c ^ orderOf z = 1 := by
    have := key (orderOf z)
    rw [pow_orderOf_eq_one] at this
    simpa using this.symm
  have hcP : c ∈ P := hQP hcQ
  obtain ⟨k, hk⟩ := hP ⟨c, hcP⟩
  have hk' : c ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) (orderOf z) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hz)
  have hd : orderOf c ∣ Nat.gcd (2 ^ k) (orderOf z) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h1)
  rw [hcop] at hd
  have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  rw [h3, hc1, one_mul]

theorem normal_closure_K (h : Setup28 W K S) (hR : Red28 W K S) {p : X} (hp : p ∈ K)
    (hpz : p ∉ zPre W K) (hE : ∀ w ∈ kerAct W K S, ⁅p, w⁆ ∈ vOf W K S) :
    ∀ k ∈ K, ∀ w ∈ kerAct W K S, ⁅k, w⁆ ∈ vOf W K S := by
  have hvN : ∀ n ∈ K ⊔ S, ∀ v ∈ vOf W K S, n * v * n⁻¹ ∈ vOf W K S := hR.v_nrm
  let E : Subgroup X :=
    { carrier := {x | x ∈ K ∧ ∀ w ∈ kerAct W K S, ⁅x, w⁆ ∈ vOf W K S}
      one_mem' := ⟨K.one_mem, fun w _ => by simpa using (vOf W K S).one_mem⟩
      mul_mem' := by
        rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
        refine ⟨K.mul_mem haK hbK, fun w hw => ?_⟩
        have h1 : ⁅a * b, w⁆ = (a * ⁅b, w⁆ * a⁻¹) * ⁅a, w⁆ := by
          simp only [commutatorElement_def]; group
        rw [h1]
        exact (vOf W K S).mul_mem (hvN a (Subgroup.mem_sup_left haK) _ (hb w hw)) (ha w hw)
      inv_mem' := by
        rintro a ⟨haK, ha⟩
        refine ⟨K.inv_mem haK, fun w hw => ?_⟩
        have h1 : ⁅a⁻¹, w⁆ = a⁻¹ * (⁅a, w⁆⁻¹) * a := by
          simp only [commutatorElement_def]; group
        rw [h1]
        simpa using hvN a⁻¹ (Subgroup.mem_sup_left (K.inv_mem haK)) _
          ((vOf W K S).inv_mem (ha w hw)) }
  have hEK : E ≤ K := fun x hx => hx.1
  have hEn : ∀ k ∈ K, ∀ m ∈ E, k * m * k⁻¹ ∈ E := by
    rintro k hk m ⟨hmK, hm⟩
    refine ⟨K.mul_mem (K.mul_mem hk hmK) (K.inv_mem hk), fun w hw => ?_⟩
    have hw' : k⁻¹ * w * k⁻¹⁻¹ ∈ kerAct W K S :=
      hR.w1_nrm k⁻¹ (Subgroup.mem_sup_left (K.inv_mem hk)) w hw
    have h1 : ⁅k * m * k⁻¹, w⁆ = k * ⁅m, k⁻¹ * w * k⁻¹⁻¹⁆ * k⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact hvN k (Subgroup.mem_sup_left hk) _ (hm _ hw')
  have hKE := InducedAux.K_le_of_normal_noncentral h hR.quasi hEK hEn (p := p) ⟨hp, hE⟩ hpz
  intro k hk w hw
  exact (hKE hk).2 w hw

theorem K_eq_comm (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) : ⁅K, Subgroup.zpowers a⁆ = K := by
  have haN : a ∈ Subgroup.normalizer (K : Set X) := h.hN haS
  have hzp : Subgroup.zpowers a ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.zpowers_le).mpr haN
  have hMK : ⁅K, Subgroup.zpowers a⁆ ≤ K := by
    refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    have h1 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ K :=
      ((Subgroup.mem_normalizer_iff.mp (hzp hg₂)) g₁⁻¹).mp (K.inv_mem hg₁)
    have h2 : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [h2]
    exact K.mul_mem hg₁ h1
  have hMn : ∀ k ∈ K, ∀ m ∈ ⁅K, Subgroup.zpowers a⁆, k * m * k⁻¹ ∈ ⁅K, Subgroup.zpowers a⁆ := by
    intro k hk
    have : ⁅K, Subgroup.zpowers a⁆ ≤ (⁅K, Subgroup.zpowers a⁆).comap (MulAut.conj k).toMonoidHom := by
      refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
      rw [Subgroup.mem_comap]
      have h1 : k * ⁅g₁, g₂⁆ * k⁻¹ = ⁅k * g₁, g₂⁆ * ⁅k, g₂⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      show k * ⁅g₁, g₂⁆ * k⁻¹ ∈ _
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (K.mul_mem hk hg₁) hg₂)
        (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hk hg₂))
    intro m hm
    exact this hm
  have hnz : ∃ m ∈ ⁅K, Subgroup.zpowers a⁆, m ∉ zPre W K := by
    by_contra hcon
    push Not at hcon
    have h1 : ⁅⁅K, Subgroup.zpowers a⁆, K⁆ ≤ W :=
      Subgroup.commutator_le.mpr fun m hm k hk => (hcon m hm).2 k hk
    have h2 : ⁅⁅Subgroup.zpowers a, K⁆, K⁆ ≤ W := by
      rw [Subgroup.commutator_comm (Subgroup.zpowers a) K]; exact h1
    have h3 := CFSG.SignalizerFunctorTheorem.McBride.three_subgroups_lemma_normal
      (X := K) (Y := Subgroup.zpowers a) (Z := K) (N := W) h1 h2
    rw [h.hK.2.1] at h3
    apply hna
    refine ⟨haS, fun k hk => ?_⟩
    have h4 : ⁅k, a⁆ ∈ W := (Subgroup.commutator_le.mp h3) k hk a (Subgroup.mem_zpowers a)
    have h5 : ⁅a, k⁆ = ⁅k, a⁆⁻¹ := (commutatorElement_inv k a).symm
    rw [h5]
    exact W.inv_mem h4
  obtain ⟨m, hm, hmz⟩ := hnz
  exact le_antisymm hMK (InducedAux.K_le_of_normal_noncentral h hR.quasi hMK hMn hm hmz)

theorem c1_outer (h : Setup28 W K S) (h1 : Hyp28One W K S) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) : ¬ IndInner W K a := by
  rintro ⟨k, hk, hik⟩
  apply hna
  have hconj := InducedAux.indHom_of_indInner h haS hk hik
  have hmem : InducedAux.indHom W K S h.hN ⟨a, haS⟩ ∈
      indAut W K S ⊓ (MulAut.conj : ↥(bar W K) →* MulAut ↥(bar W K)).range :=
    ⟨InducedAux.indHom_mem h haS, ⟨_, hconj.symm⟩⟩
  rw [h1.2.2, Subgroup.mem_bot] at hmem
  exact InducedAux.mem_kerAct_of_indHom_eq_one h haS hmem

theorem c2_outer (h : Setup28 W K S) (h2 : Hyp28Two W K S) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) : ¬ IndInner W K a := by
  rintro ⟨k, hk, hik⟩
  obtain ⟨⟨hq, m, hm5, ⟨e₀⟩⟩, _, _, _, n, e, _, τ, hτ, hact⟩ := h2
  have hn4 : 4 ≤ n := InducedAux.four_le_of_equiv_alternatingGroup hm5 e₀ e
  have hperf : commutator ↥(bar W K) = ⊤ := hq.1.commutator_eq_top
  have hconj := InducedAux.indHom_of_indInner h haS hk hik
  obtain ⟨σ, hσ, hind⟩ := hact.1 _ (InducedAux.indHom_mem h haS)
  set c : ↥(alternatingGroup (Fin n)) := e (QuotientGroup.mk (toBar W K ⟨k, hk⟩)) with hc
  have hσc : σ = MulAut.conj c := by
    ext y
    obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective (e.symm y)
    have hy : e (QuotientGroup.mk z) = y := by rw [hz]; simp
    rw [← hy, ← hind z, hconj]
    simp [hc]
  have hτ2 : τ ^ 2 = 1 := by rw [← hτ.orderOf]; exact pow_orderOf_eq_one τ
  have hcn2 : (MulAut.conjNormal (H := alternatingGroup (Fin n)) τ) ^ 2 = 1 := by
    rw [← map_pow, hτ2, map_one]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hσ
  have hcases : σ = 1 ∨ σ = MulAut.conjNormal (H := alternatingGroup (Fin n)) τ := by
    have hjj : j = j % 2 + 2 * (j / 2) := (Int.emod_add_mul_ediv j 2).symm
    have hx : (MulAut.conjNormal (H := alternatingGroup (Fin n)) τ) ^ (2 * (j / 2)) = 1 := by
      rw [zpow_mul]
      have : (MulAut.conjNormal (H := alternatingGroup (Fin n)) τ) ^ (2 : ℤ) = 1 := by
        simpa using hcn2
      rw [this, one_zpow]
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · left
      rw [← hj, hjj, zpow_add, hx, h0]; simp
    · right
      rw [← hj, hjj, zpow_add, hx, h1]; simp
  rcases hcases with h1 | h1
  ·
    have hφ1 : InducedAux.indHom W K S h.hN ⟨a, haS⟩ = 1 := by
      refine InducedAux.aut_eq_one hperf le_rfl _ fun x => ?_
      have h2 := hind x
      rw [h1, MulAut.one_apply] at h2
      exact QuotientGroup.eq.mp (e.injective h2).symm
    exact hna (InducedAux.mem_kerAct_of_indHom_eq_one h haS hφ1)
  ·
    have h3 : MulAut.conjNormal (H := alternatingGroup (Fin n)) (c : Equiv.Perm (Fin n)) =
        MulAut.conjNormal (H := alternatingGroup (Fin n)) τ := by
      rw [MulAut.conjNormal_val, ← hσc, h1]
    have h4 := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n hn4 h3
    have h5 : Equiv.Perm.sign τ = 1 := by
      rw [← h4]; exact Equiv.Perm.mem_alternatingGroup.mp c.2
    rw [hτ.sign_eq] at h5
    exact absurd h5 (by decide)

end Toolbox

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
