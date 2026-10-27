module

public import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.FrobeniusNormalComplement
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeOmega

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N

open CFSG.Open Subgroup

section NPC

theorem hasNormalPComplement_of_fix_omega {K : Type*} [Group K] [Finite K] {p : ℕ}
    [hp : Fact p.Prime] (hodd : p ≠ 2)
    (hfix : ∀ Q : Subgroup K, IsPGroup p Q → ∀ n ∈ normalizer (Q : Set K), ∀ x ∈ Q, x ^ p = 1 →
      n * x * n⁻¹ = x) : CFSG.HasNormalPComplement p K := by
  rw [CFSG.GroupTheory.hasNormalPComplement_iff_isPGroup_automizer]
  intro Q hQ
  apply CFSG.SectionRank.Ccomm.isPGroup_of_coprime_eq_one
  intro a ha
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective a
  set C : Subgroup (Subgroup.normalizer (Q : Set K)) :=
    (Subgroup.centralizer (Q : Set K)).subgroupOf (Subgroup.normalizer (Q : Set K)) with hC
  have hker : (Q.normalizerMonoidHom).ker = C := Subgroup.normalizerMonoidHom_ker Q
  have : C.Normal := by rw [← hker]; infer_instance
  let ψ : (Subgroup.normalizer (Q : Set K)) ⧸ C →* MulAut Q :=
    QuotientGroup.lift C Q.normalizerMonoidHom (by rw [← hker])
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : Q.normalizerMonoidHom m = 1 := hx
    rw [QuotientGroup.eq_one_iff, ← hker]
    exact h1
  have hψn : ψ (QuotientGroup.mk n) = Q.normalizerMonoidHom n := rfl
  have hcop : (orderOf (Q.normalizerMonoidHom n)).Coprime p := by
    rw [← hψn, orderOf_injective ψ hψ]
    exact ha
  have hα : Q.normalizerMonoidHom n = 1 := by
    refine CFSG.HardMathSupport.Timmesfeld.ComponentBalance.mulAut_eq_one_of_coprime_of_fix_omega
      hodd hQ hcop ?_
    intro x hx
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hfix Q hQ n n.2 x x.2 (by rw [← Subgroup.coe_pow, hx, Subgroup.coe_one])
  rw [QuotientGroup.eq_one_iff]
  have hnC : n ∈ C := by rw [← hker]; exact hα
  exact hnC

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

theorem mem_normalizer_of_conj_mem {Q : Subgroup G} {g : G}
    (hg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) : g ∈ normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨q, hq, rfl⟩
    exact hg q hq
  · rw [Nat.card_congr (Subgroup.equivMapOfInjective Q (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv]
    exact le_rfl

theorem le_normalizer_and_mem_of_elemAbelian {Q : Subgroup G} (hQ : IsElemAbelian p Q)
    (hmax : ∀ g : G, g ^ p = 1 → (∀ q ∈ Q, q * g = g * q) → g ∈ Q)
    (hN : ∀ g ∈ normalizer (Q : Set G), ∀ q ∈ Q, g * q * g⁻¹ = q)
    (P : Sylow p G) (hQP : Q ≤ P) :
    (P : Subgroup G) ≤ normalizer (Q : Set G) ∧ ∀ g ∈ (P : Subgroup G), g ^ p = 1 → g ∈ Q := by
  set R : Subgroup G := (P : Subgroup G) ⊓ normalizer (Q : Set G) with hR
  have hRQ : ∀ r ∈ R, r ^ p = 1 → r ∈ Q := by
    intro r hr hr3
    refine hmax r hr3 fun q hq => ?_
    have h1 := hN r (Subgroup.mem_inf.1 hr).2 q hq
    calc q * r = r * q * r⁻¹ * r := by rw [h1]
      _ = r * q := by group
  have hQR : Q ≤ R := le_inf hQP Subgroup.le_normalizer
  suffices hRP : R = P by
    refine ⟨fun g hg => ?_, fun g hg hg3 => hRQ g (hRP ▸ hg) hg3⟩
    rw [← hRP] at hg
    exact (Subgroup.mem_inf.1 hg).2
  haveI hnil : Group.IsNilpotent ↥(P : Subgroup G) := P.isPGroup'.isNilpotent
  have hnc := (normalizerCondition_iff_only_full_group_self_normalizing.1
    (normalizerCondition_of_isNilpotent (G := ↥(P : Subgroup G)))) (R.subgroupOf P)
  have hself : normalizer ((R.subgroupOf P : Subgroup ↥(P : Subgroup G)) :
      Set ↥(P : Subgroup G)) = R.subgroupOf P := by
    refine le_antisymm (fun n hn => ?_) Subgroup.le_normalizer
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.2 ⟨n.2, mem_normalizer_of_conj_mem fun q hq => ?_⟩
    have hqR : (⟨q, hQP hq⟩ : ↥(P : Subgroup G)) ∈ R.subgroupOf P :=
      Subgroup.mem_subgroupOf.2 (hQR hq)
    have h1 := (Subgroup.mem_normalizer_iff.1 hn ⟨q, hQP hq⟩).1 hqR
    rw [Subgroup.mem_subgroupOf] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    refine hRQ _ h1 ?_
    rw [conj_pow, hQ.2 q hq, mul_one, mul_inv_cancel]
  have htop := hnc hself
  exact le_antisymm inf_le_left (Subgroup.subgroupOf_eq_top.1 htop)

theorem hasNormalPComplement_of_elemAbelian (hodd : p ≠ 2) {Q : Subgroup G}
    (hQ : IsElemAbelian p Q)
    (hmax : ∀ g : G, g ^ p = 1 → (∀ q ∈ Q, q * g = g * q) → g ∈ Q)
    (hN : ∀ g ∈ normalizer (Q : Set G), ∀ q ∈ Q, g * q * g⁻¹ = q) :
    CFSG.HasNormalPComplement p G := by
  have hQp : IsPGroup p Q := fun q => ⟨1, Subtype.ext (by simpa using hQ.2 q q.2)⟩
  obtain ⟨P, hQP⟩ := hQp.exists_le_sylow
  obtain ⟨hPN, hPQ⟩ := le_normalizer_and_mem_of_elemAbelian hQ hmax hN P hQP
  have hcube : ∀ m q : G, q ^ p = 1 → (m * q * m⁻¹) ^ p = 1 := fun m q hq => by
    rw [conj_pow, hq, mul_one, mul_inv_cancel]
  have hQC : ∀ q ∈ Q, q ∈ centralizer ((P : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 := hN r (hPN hr) q hq
    calc r * q = r * q * r⁻¹ * r := by group
      _ = q * r := by rw [h1]
  have hNPQ : ∀ m ∈ normalizer ((P : Subgroup G) : Set G), ∀ q ∈ Q, m * q * m⁻¹ = q := by
    intro m hm q hq
    refine hN m (mem_normalizer_of_conj_mem fun q' hq' => ?_) q hq
    exact hPQ _ ((Subgroup.mem_normalizer_iff.1 hm q').1 (hQP hq')) (hcube m q' (hQ.2 q' hq'))
  apply hasNormalPComplement_of_fix_omega hodd
  intro H hH n hn x hx hx3
  obtain ⟨P₀, hHP₀⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P
  have hconj : ∀ u ∈ H, g * u * g⁻¹ ∈ (P : Subgroup G) := by
    intro u hu
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨u, hHP₀ hu, rfl⟩
  have hnx : n * x * n⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hn x).1 hx
  have hx'Q : g * x * g⁻¹ ∈ Q := hPQ _ (hconj x hx) (hcube g x hx3)
  have hy'Q : g * (n * x * n⁻¹) * g⁻¹ ∈ Q :=
    hPQ _ (hconj _ hnx) (hcube g _ (hcube n x hx3))
  set n' := g * n * g⁻¹ with hn'
  have hy'eq : n'⁻¹⁻¹ * (g * x * g⁻¹) * n'⁻¹ = g * (n * x * n⁻¹) * g⁻¹ := by
    rw [hn']
    group
  obtain ⟨m, hm, hmeq⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer P (g * x * g⁻¹) n'⁻¹
    (hQC _ hx'Q) (by rw [hy'eq]; exact hQC _ hy'Q)
  have h1 := hNPQ m⁻¹ (inv_mem hm) _ hx'Q
  rw [inv_inv] at h1
  rw [hy'eq, h1] at hmeq
  calc n * x * n⁻¹ = g⁻¹ * (g * (n * x * n⁻¹) * g⁻¹) * g := by group
    _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hmeq]
    _ = x := by group

end NPC

section Pair

variable {X : Type} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]

theorem isElemAbelian_zpowers {c : X} (hc : c ^ p = 1) : IsElemAbelian p (zpowers c) := by
  rw [Subgroup.zpowers_eq_closure]
  refine IsElemAbelian.closure_of_commute (fun u hu w hw => ?_) (fun u hu => ?_)
  · rw [Set.mem_singleton_iff] at hu hw
    rw [hu, hw]
  · rw [Set.mem_singleton_iff] at hu
    rw [hu, hc]

theorem hasNormalPComplement_of_pair (hodd : p ≠ 2) {x v : X}
    (hrank : CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) (hx : x ^ p = 1)
    (hv : v ^ p = 1) (hv1 : v ≠ 1) (hvx : v * x = x * v) (hxv : x ∉ zpowers v)
    (hN : ∀ g ∈ centralizer ({x} : Set X),
      g ∈ normalizer ((zpowers v ⊔ zpowers x : Subgroup X) : Set X) → g * v * g⁻¹ = v) :
    CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set X)) := by
  set C := centralizer ({x} : Set X) with hCdef
  set Q : Subgroup X := zpowers v ⊔ zpowers x with hQdef
  have hcomm : ∀ a ∈ zpowers v, ∀ b ∈ zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((Commute.zpow_left hvx i).zpow_right j).eq
  have hQ : IsElemAbelian p Q :=
    (isElemAbelian_zpowers hv).sup_of_commute (isElemAbelian_zpowers hx) hcomm
  have hQp2 : Nat.card Q = p ^ 2 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp.out (zpowers v) hx hxv
      (fun a ha => hcomm a ha x (Subgroup.mem_zpowers x)), Nat.card_zpowers,
      orderOf_eq_prime hv hv1, pow_two]
  have hQC : Q ≤ C := fun q hq => mem_centralizer_singleton_iff.2
    (hQ.comm hq (le_sup_right (a := zpowers v) (Subgroup.mem_zpowers x)))
  refine hasNormalPComplement_of_elemAbelian (G := ↥C) hodd (Q := Q.subgroupOf C)
    (hQ.comap C.subtype_injective) ?_ ?_
  ·
    intro g hgp hgQ
    by_contra hgQ'
    have hgQ'' : (g : X) ∉ Q := fun h => hgQ' (Subgroup.mem_subgroupOf.2 h)
    have hgp' : (g : X) ^ p = 1 := by rw [← Subgroup.coe_pow, hgp, Subgroup.coe_one]
    have hcg : ∀ q ∈ Q, q * (g : X) = (g : X) * q := fun q hq =>
      congrArg Subtype.val (hgQ ⟨q, hQC hq⟩ (Subgroup.mem_subgroupOf.2 hq))
    have hW : IsElemAbelian p (Q ⊔ zpowers (g : X)) :=
      hQ.sup_of_commute (isElemAbelian_zpowers hgp')
        (fun a ha b hb => by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
          exact (Commute.zpow_right (hcg a ha) k).eq)
    have hW27 : Nat.card ↥(Q ⊔ zpowers (g : X)) = p ^ 3 := by
      rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp.out Q hgp' hgQ'' hcg, hQp2]
      ring
    have hWC : Q ⊔ zpowers (g : X) ≤ C := sup_le hQC (zpowers_le.2 g.2)
    have := CFSG.SectionRank.le_pRank hp.out.one_lt hWC hW hW27
    omega
  ·
    intro g hg q hq
    have hgX : (g : X) ∈ normalizer (Q : Set X) := by
      refine mem_normalizer_of_conj_mem fun q' hq' => ?_
      have h1 := (Subgroup.mem_normalizer_iff.1 hg ⟨q', hQC hq'⟩).1
        (Subgroup.mem_subgroupOf.2 hq')
      exact Subgroup.mem_subgroupOf.1 h1
    have hgv := hN g g.2 hgX
    have hgx : (g : X) * x * (g : X)⁻¹ = x := by
      have := mem_centralizer_singleton_iff.1 g.2
      rw [this, mul_inv_cancel_right]
    have hle : Q ≤ centralizer ({(g : X)} : Set X) := sup_le
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 (by
        calc v * (g : X) = (g : X) * v * (g : X)⁻¹ * (g : X) := by rw [hgv]
          _ = (g : X) * v := by group)))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 (by
        calc x * (g : X) = (g : X) * x * (g : X)⁻¹ * (g : X) := by rw [hgx]
          _ = (g : X) * x := by group)))
    have hq' : (q : X) * (g : X) = (g : X) * q :=
      mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_subgroupOf.1 hq))
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hq', mul_inv_cancel_right]

end Pair

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N
