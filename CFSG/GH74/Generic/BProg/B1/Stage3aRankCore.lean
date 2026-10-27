module

public import CFSG.GH74.Generic.BProg.B1.Assembly2
import CFSG.GH74.Generic.BProg.B1.JPrime
import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.GH74.Generic.JMaxCongr

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

theorem rankCertified_zpowers_involution {X : Type} [Group X] [Finite X] {a : X} (haa : a * a = 1)
    (ha1 : a ≠ 1) : RankCertified ↥(zpowers a) 0 := by
  have hord : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact haa) ha1
  have ha2 : a ^ 2 = 1 := by rw [sq]; exact haa
  refine ⟨↥(zpowers a), ↥(zpowers a), inferInstance, inferInstance, inferInstance,
    MonoidHom.id _, MonoidHom.id _, Function.surjective_id, ?_, ?_, ?_, le_rfl⟩
  · intro g h
    exact mul_comm' g h
  · intro g
    obtain ⟨g, k, rfl⟩ := g
    apply Subtype.ext
    show ((a ^ k) ^ 2 : X) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [ha2]
  · rw [Nat.card_zpowers, hord]
    norm_num

theorem eq_one_or_eq_of_mem_zpowers_two {X : Type} [Group X] {a p : X} (haa : a * a = 1)
    (hp : p ∈ zpowers a) : p = 1 ∨ p = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
  have ha2 : a ^ 2 = 1 := by rw [sq]; exact haa
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
    rw [zpow_mul, zpow_two, ← sq, ha2, one_zpow]
  · right
    obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
    rw [zpow_add_one, zpow_mul, zpow_two, ← sq, ha2, one_zpow, one_mul]

theorem rankCertified_of_commuting_range {X : Type} [Group X] {K : Subgroup X} {Y : Type}
    [Group Y] {r s : ℕ} (hK : RankCertified ↥K r) (hY : RankCertified Y s) (ψ : Y →* X)
    (hcomm : ∀ k ∈ K, ∀ y : Y, k * ψ y = ψ y * k) (hker : ∀ y : Y, ψ y ∈ K → y = 1) :
    RankCertified X (r + s + 1) := by
  let φ : ↥K × Y →* X := MonoidHom.noncommCoprod K.subtype ψ (fun k y => hcomm _ k.2 y)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨k, y⟩ h
    have h1 : (k : X) * ψ y = 1 := h
    have hk : ψ y ∈ K := by
      have : ψ y = (k : X)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact K.inv_mem k.2
    have hy := hker y hk
    subst hy
    rw [map_one, mul_one] at h1
    exact Prod.ext (Subtype.ext h1) rfl
  exact (hK.prod hY).of_injective φ hφ

theorem false_of_central_involution_pair {X : Type} [Group X] [Finite X] (hX : Gen4 X)
    {K : Subgroup X} {a b : X} (haa : a * a = 1) (hbb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hac : ∀ y : X, y * a = a * y) (hbK : ∀ k ∈ K, b * k = k * b) {r : ℕ}
    (hK : RankCertified ↥K r)
    (hZ : ∀ z ∈ Subgroup.center ↥K, (z : X) = 1 ∨ (z : X) = a) (hr2 : 2 ≤ r)
    (hr3 : a ∈ K → 3 ≤ r) : False := by
  have hbnK : b ∉ K := by
    intro hb
    have hcen : (⟨b, hb⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hbK g g.2).symm
    rcases hZ _ hcen with h | h
    · exact hb1 h
    · exact hab h.symm
  by_cases haK : a ∈ K
  · have hY : RankCertified ↥(zpowers b) 0 := rankCertified_zpowers_involution hbb hb1
    have hX4 : RankCertified X (r + 0 + 1) := by
      refine rankCertified_of_commuting_range hK hY (zpowers b).subtype (fun k hk y => ?_)
        (fun y hy => ?_)
      · obtain ⟨y, hy⟩ := y
        rcases eq_one_or_eq_of_mem_zpowers_two hbb hy with rfl | rfl
        · simp
        · exact (hbK k hk).symm
      · obtain ⟨y, hy'⟩ := y
        rcases eq_one_or_eq_of_mem_zpowers_two hbb hy' with rfl | rfl
        · rfl
        · exact absurd hy hbnK
    exact hX4.not_gen4 (by have := hr3 haK; omega) hX
  · have hcommAB : ∀ (p : ↥(zpowers a)) (q : ↥(zpowers b)), Commute (p : X) (q : X) := by
      intro p q
      rcases eq_one_or_eq_of_mem_zpowers_two haa p.2 with h | h
      · rw [h]
        exact Commute.one_left _
      · rw [h]
        exact (hac q).symm
    let ψ : ↥(zpowers a) × ↥(zpowers b) →* X :=
      MonoidHom.noncommCoprod (zpowers a).subtype (zpowers b).subtype hcommAB
    have hψ : ∀ y : ↥(zpowers a) × ↥(zpowers b), ψ y = (y.1 : X) * (y.2 : X) := fun y => rfl
    have hY : RankCertified (↥(zpowers a) × ↥(zpowers b)) (0 + 0 + 1) :=
      (rankCertified_zpowers_involution haa ha1).prod (rankCertified_zpowers_involution hbb hb1)
    have hX4 : RankCertified X (r + (0 + 0 + 1) + 1) := by
      refine rankCertified_of_commuting_range hK hY ψ (fun k hk y => ?_) (fun y hy => ?_)
      · rw [hψ]
        have h1 : Commute k (y.1 : X) := by
          rcases eq_one_or_eq_of_mem_zpowers_two haa y.1.2 with h | h
          · rw [h]
            exact Commute.one_right _
          · rw [h]
            exact hac k
        have h2 : Commute k (y.2 : X) := by
          rcases eq_one_or_eq_of_mem_zpowers_two hbb y.2.2 with h | h
          · rw [h]
            exact Commute.one_right _
          · rw [h]
            exact (hbK k hk).symm
        exact h1.mul_right h2
      · obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := y
        rw [hψ] at hy
        change p * q ∈ K at hy
        rcases eq_one_or_eq_of_mem_zpowers_two haa hp with hp1 | hpa <;>
          rcases eq_one_or_eq_of_mem_zpowers_two hbb hq with hq1 | hqb
        · subst hp1
          subst hq1
          rfl
        · subst hp1
          rw [hqb, one_mul] at hy
          exact absurd hy hbnK
        · subst hq1
          rw [hpa, mul_one] at hy
          exact absurd hy haK
        · rw [hpa, hqb] at hy
          have hcen : (⟨a * b, hy⟩ : ↥K) ∈ Subgroup.center ↥K := by
            rw [Subgroup.mem_center_iff]
            intro g
            apply Subtype.ext
            show (g : X) * (a * b) = a * b * (g : X)
            rw [← mul_assoc, hac g, mul_assoc, ← hbK g g.2, ← mul_assoc]
          exfalso
          rcases hZ _ hcen with h | h
          · exact hab ((eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right haa)).symm
          · exact hb1 (mul_left_cancel (h.trans (mul_one a).symm))
    exact hX4.not_gen4 (by omega) hX

theorem exists_involution_bar {G : Type} [Group G] [Finite G] {x : G} (hx : orderOf x = 2)
    {K : Subgroup G} (hKpc : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hr : 1 < pRank 2 ↥(CxK x K)) :
    ∃ eb : CentralizerBar x, eb * eb = 1 ∧ eb ≠ 1 ∧ eb ≠ xbar x ∧
      ∀ w ∈ imgBar x K, eb * w = w * eb := by
  obtain ⟨a, b, haH, hbH, ha2, hb2, hab, hne⟩ :=
    CFSG.GH74.GLS.Stage1.Thm2.Recip.exists_two_involutions_of_two_le_pRank
      (Nat.succ_le_of_lt hr)
  obtain ⟨e, heH, he2, hex⟩ : ∃ e : G, e ∈ CxK x K ∧ orderOf e = 2 ∧ e ≠ x := by
    by_cases hax : a = x
    · exact ⟨b, hbH, hb2, fun h => hne (hax.trans h.symm)⟩
    · exact ⟨a, haH, ha2, hax⟩
  have heC : e ∈ centralizer ({x} : Set G) := (Subgroup.mem_inf.1 heH).1
  have hee : e * e = 1 := by
    have := pow_orderOf_eq_one e
    rwa [he2, pow_two] at this
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  refine ⟨proj x ⟨e, heC⟩, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul]
    have : (⟨e, heC⟩ : ↥(centralizer ({x} : Set G))) * ⟨e, heC⟩ = 1 := Subtype.ext hee
    rw [this, map_one]
  · intro h1
    have h2 : proj x ⟨e, heC⟩ = proj x ⟨1, one_mem _⟩ := by
      rw [h1]
      exact (map_one (proj x)).symm
    have h3 := eq_of_proj_eq_of_involutions heC (one_mem _) hee (one_mul 1)
      (by rw [mul_one, one_mul]) h2
    rw [h3, orderOf_one] at he2
    omega
  · intro h4
    exact hex (eq_of_proj_eq_of_involutions heC hxC hee hxx
      (Subgroup.mem_centralizer_singleton_iff.1 heC) h4)
  · intro w hw
    obtain ⟨g, hgK, rfl⟩ := mem_imgBar.1 hw
    have h1 := CFSG.GH74.GLS.C3.Layer1.PumpCalc.map_eq_of_mem_cSec hKpc heC
      (Subgroup.mem_inf.1 heH).2 g (Subgroup.mem_subgroupOf.2 hgK)
    have h2 : proj x ⟨e, heC⟩ * proj x g * (proj x ⟨e, heC⟩)⁻¹ = proj x g := by
      simp only [map_mul, map_inv] at h1
      exact h1
    exact mul_inv_eq_iff_eq_mul.1 h2

theorem false_of_J2_pair_rank {G : Type} [Group G] [Finite G] (hgen : Gen4 G) {x : G}
    (hx : orderOf x = 2) {K : Subgroup G} (hKpc : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hr : 1 < pRank 2 ↥(CxK x K)) {r : ℕ} (hcert : RankCertified ↥(imgBar x K) r)
    (hZ : ∀ z ∈ Subgroup.center ↥(imgBar x K),
      (z : CentralizerBar x) = 1 ∨ (z : CentralizerBar x) = xbar x)
    (hr2 : 2 ≤ r) (hr3 : xbar x ∈ imgBar x K → 3 ≤ r) : False := by
  obtain ⟨eb, hee, he1, hex, hcent⟩ := exists_involution_bar hx hKpc hr
  exact false_of_central_involution_pair (gen4_centralizerBar hgen x) (xbar_mul_self hx) hee
    (xbar_ne_one hx) he1 (Ne.symm hex) (fun y => xbar_comm x y) hcent hcert hZ hr2 hr3

theorem false_of_J2_pair_rank_of_center_bot {G : Type} [Group G] [Finite G] (hgen : Gen4 G)
    {x : G} (hx : orderOf x = 2) {K : Subgroup G}
    (hKpc : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hr : 1 < pRank 2 ↥(CxK x K))
    (hbot : Subgroup.center ↥(imgBar x K) = ⊥) (hcert : RankCertified ↥(imgBar x K) 2) : False :=
  false_of_J2_pair_rank hgen hx hKpc hr hcert
    (fun z hz => by
      rw [hbot, Subgroup.mem_bot] at hz
      exact Or.inl (by rw [hz]; rfl))
    le_rfl (fun h => absurd h (xbar_not_mem_of_center_eq_bot hx hbot))

theorem noJPrimeFor_of_bar {P : ∀ (Kt : Type) [Group Kt], Prop}
    (hP : ∀ {A B : Type} [Group A] [Group B], A ≃* B → P A → P B)
    (h : ∀ (G : Type) [Group G] [Finite G], Gen4 G → ∀ (x : G) (K : Subgroup G), orderOf x = 2 →
      IsPCompIn 2 (centralizer ({x} : Set G)) K → InG2 ↥(imgBar x K) →
        1 < pRank 2 ↥(CxK x K) → P ↥(imgBar x K) → False) : NoJPrimeFor P := by
  intro G _ _ hyp _ x K hJ hr hPK
  have hILo : IsILo 2 x K := hJ.1.1
  have hx : orderOf x = 2 := hILo.1
  have hKpc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hILo.2.2
  have hG2K : InG2 (↥K ⧸ pPrimeCore 2 ↥K) := hJ.1.2
  obtain ⟨eMK⟩ := CFSG.GH74.GLS.C3.Layer1.PumpCalc.kBar_equiv_bar hKpc
  have eMK' : (↥K ⧸ pPrimeCore 2 ↥K) ≃* ↥(imgBar x K) := eMK
  exact h G hyp.gen4 x K hx hKpc (inG2_of_mulEquiv eMK' hG2K) hr (hP eMK' hPK)

end CFSG.GH74.Generic.BProg.B1
