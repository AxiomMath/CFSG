module

public import CFSG.LocalAnalysis.GLTheoremA.Lemma48
public import CFSG.LocalAnalysis.GLTheoremA.Sec5A

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace Prop53

section Group

variable {G : Type} [Group G]

theorem isCyclic_of_forall_conj_mem {S P : Subgroup G} (hP : IsCyclic P) (w : G)
    (h : ∀ s ∈ S, w⁻¹ * s * w ∈ P) : IsCyclic S := by
  let f : S →* P :=
    { toFun := fun s => ⟨w⁻¹ * s * w, h s s.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [mul_assoc] }
  refine isCyclic_of_injective f ?_
  intro a b hab
  have h1 := congrArg Subtype.val hab
  have h2 : w⁻¹ * (a : G) * w = w⁻¹ * (b : G) * w := h1
  exact Subtype.ext (by simpa using h2)

theorem isElemAbelian_zpowers {p : ℕ} {a : G} (ha : a ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers a) := by
  refine ⟨inferInstance, fun g hg => ?_⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]

theorem mem_centralizer_zpowers_of_comm {a b : G} (hab : a * b = b * a) :
    a ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  exact (Commute.zpow_left (show Commute b a from hab.symm) k).eq

theorem mem_normalizer_zpowers_of_comm {a b : G} (hab : a * b = b * a) :
    a ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
  Subgroup.centralizer_le_normalizer _ (mem_centralizer_zpowers_of_comm hab)

theorem mem_centralizer_of_le_centralizer {D : Subgroup G} {b : G}
    (h : D ≤ Subgroup.centralizer ({b} : Set G)) : b ∈ Subgroup.centralizer (D : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact Subgroup.mem_centralizer_singleton_iff.1 (h hd)

theorem mem_normalizer_inf_of_mem {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hH h, hK h]

theorem le_of_sylow_of_isPGroup {p : ℕ} (hp : p.Prime) {W Q R : Subgroup G} (hQR : Q ≤ R)
    (hRW : R ≤ W) (hR : IsPGroup p R) (hQp : IsPGroup p Q) (hQi : ¬ p ∣ Q.relIndex W) :
    R ≤ Q := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hQ' : IsPGroup p (Q.subgroupOf W) := hQp.comap_subtype
  let Qs : Sylow p W := hQ'.toSylow hQi
  have hR' : IsPGroup p (R.subgroupOf W) := hR.comap_subtype
  have hle : (Qs : Subgroup W) ≤ R.subgroupOf W := fun a ha =>
    Subgroup.mem_subgroupOf.2 (hQR (Subgroup.mem_subgroupOf.1 ha))
  have heq : R.subgroupOf W = Qs := Qs.is_maximal' hR' hle
  intro r hr
  have h1 : (⟨r, hRW hr⟩ : W) ∈ R.subgroupOf W := Subgroup.mem_subgroupOf.2 hr
  rw [heq] at h1
  exact Subgroup.mem_subgroupOf.1 h1

theorem isElemAbelian_sup_of_commute {p : ℕ} {D C : Subgroup G} (hD : IsElemAbelian p D)
    (hC : IsElemAbelian p C) (hcomm : ∀ d ∈ D, ∀ c ∈ C, d * c = c * d) :
    IsElemAbelian p (D ⊔ C) := by
  have hnorm : D ≤ Subgroup.normalizer (C : Set G) := by
    intro d hd
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (hcomm d hd c hc).symm
  have hdec : ∀ x ∈ D ⊔ C, ∃ d ∈ D, ∃ c ∈ C, x = d * c := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right D C hnorm] at hx
    obtain ⟨d, hd, c, hc, rfl⟩ := Set.mem_mul.mp hx
    exact ⟨d, hd, c, hc, rfl⟩
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨d₁, hd₁, c₁, hc₁, hx⟩ := hdec x x.2
    obtain ⟨d₂, hd₂, c₂, hc₂, hy⟩ := hdec y y.2
    change (x : G) * y = y * x
    rw [hx, hy]
    calc d₁ * c₁ * (d₂ * c₂) = d₁ * (c₁ * d₂) * c₂ := by group
      _ = d₁ * (d₂ * c₁) * c₂ := by rw [← hcomm d₂ hd₂ c₁ hc₁]
      _ = (d₁ * d₂) * (c₁ * c₂) := by group
      _ = (d₂ * d₁) * (c₂ * c₁) := by
        rw [isElemAbelian_commute hD hd₁ hd₂, isElemAbelian_commute hC hc₁ hc₂]
      _ = d₂ * (d₁ * c₂) * c₁ := by group
      _ = d₂ * (c₂ * d₁) * c₁ := by rw [hcomm d₁ hd₁ c₂ hc₂]
      _ = d₂ * c₂ * (d₁ * c₁) := by group
  · obtain ⟨d, hd, c, hc, rfl⟩ := hdec x hx
    have hdc : Commute d c := hcomm d hd c hc
    rw [hdc.mul_pow, hD.2 d hd, hC.2 c hc, one_mul]

theorem mem_of_commute_of_sylow {p : ℕ} (hp : p.Prime) {W Q : Subgroup G} {x : G}
    (hQW : Q ≤ W) (hQp : IsPGroup p Q) (hQi : ¬ p ∣ Q.relIndex W) (hxW : x ∈ W)
    (hxp : x ^ p = 1) (hxc : ∀ q ∈ Q, q * x = x * q) : x ∈ Q := by
  have hxn : Subgroup.zpowers x ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hxc q hq
  have hzp : IsPGroup p (Subgroup.zpowers x) :=
    isPGroup_of_isElemAbelian (isElemAbelian_zpowers hxp)
  have hR : IsPGroup p (Q ⊔ Subgroup.zpowers x : Subgroup G) :=
    hQp.to_sup_of_normal_left' hzp hxn
  have hle := le_of_sylow_of_isPGroup hp le_sup_left
    (sup_le hQW (Subgroup.zpowers_le.2 hxW)) hR hQp hQi
  exact hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

end Group

section Finite

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_ge {p : ℕ} (hp : p.Prime) {W P₀ : Subgroup G} (hP₀W : P₀ ≤ W)
    (hP₀ : IsPGroup p P₀) :
    ∃ P : Subgroup G, P₀ ≤ P ∧ P ≤ W ∧ IsPGroup p P ∧ ¬ p ∣ P.relIndex W := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hP₀' : IsPGroup p (P₀.subgroupOf W) := hP₀.comap_subtype
  obtain ⟨Q, hQ⟩ := hP₀'.exists_le_sylow
  refine ⟨(Q : Subgroup W).map W.subtype, ?_, Subgroup.map_subtype_le _,
    Q.isPGroup'.map W.subtype, ?_⟩
  · intro a ha
    exact ⟨⟨a, hP₀W ha⟩, hQ (Subgroup.mem_subgroupOf.2 ha), rfl⟩
  · rw [Subgroup.relIndex, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective W.subtype_injective]
    exact Q.not_dvd_index

theorem exists_conj_mem_of_sylow {p : ℕ} (hp : p.Prime) {W S P : Subgroup G} (hSW : S ≤ W)
    (hS : IsPGroup p S) (hP : IsPGroup p P) (hPi : ¬ p ∣ P.relIndex W) :
    ∃ w ∈ W, ∀ s ∈ S, w⁻¹ * s * w ∈ P := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hP' : IsPGroup p (P.subgroupOf W) := hP.comap_subtype
  let Ps : Sylow p W := hP'.toSylow hPi
  have hS' : IsPGroup p (S.subgroupOf W) := hS.comap_subtype
  obtain ⟨Q, hQ⟩ := hS'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W Ps Q
  refine ⟨(g : G), g.2, fun s hs => ?_⟩
  have h2 : (⟨s, hSW hs⟩ : W) ∈ (Q : Subgroup W) := hQ (Subgroup.mem_subgroupOf.2 hs)
  rw [← hg, Sylow.coe_subgroup_smul] at h2
  obtain ⟨t, ht, hts⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 h2
  have h3 : (g : G) * (t : G) * (g : G)⁻¹ = s := by
    have := congrArg Subtype.val hts
    simpa using this
  have h4 : (g : G)⁻¹ * s * (g : G) = (t : G) := by
    rw [← h3]
    group
  rw [h4]
  exact ht

theorem isCyclic_of_inf_centralizer {p : ℕ} (hp : p.Prime) {P : Subgroup G} {x : G}
    (hP : IsPGroup p P) (hxP : x ∈ P) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hcyc : IsCyclic ↥(P ⊓ Subgroup.centralizer ({x} : Set G))) : IsCyclic P := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial P := ⟨⟨⟨x, hxP⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  have := hP.center_nontrivial
  have hpg : IsPGroup p (Subgroup.center P) :=
    hP.of_injective (Subgroup.center P).subtype (Subgroup.center P).subtype_injective
  have hdvd : p ∣ Nat.card (Subgroup.center P) := by
    obtain ⟨n, hn, hcard⟩ := hpg.nontrivial_iff_card.1 inferInstance
    rw [hcard]
    exact dvd_pow_self p hn.ne'
  obtain ⟨z₁, hz₁⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set z : G := (((z₁ : Subgroup.center P) : P) : G) with hz
  have hzP : z ∈ P := ((z₁ : Subgroup.center P) : P).2
  have hzord : orderOf z = p := by
    rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz₁]
  have hz1 : z ≠ 1 := fun h => hp.one_lt.ne' (hzord ▸ orderOf_eq_one_iff.2 h)
  have hzp : z ^ p = 1 := hzord ▸ pow_orderOf_eq_one z
  have hzcomm : ∀ g ∈ P, g * z = z * g := by
    intro g hg
    have := Subgroup.mem_center_iff.1 z₁.2 ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hzC : z ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hzcomm x hxP).symm
  have hxC : x ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hDle : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤
      P ⊓ Subgroup.centralizer ({x} : Set G) :=
    sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hxP, hxC⟩))
      (Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hzP, hzC⟩))
  have := hcyc
  have hDcyc : IsCyclic ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers z) :=
    Subgroup.isCyclic_of_le hDle
  have hxz' : Subgroup.zpowers x ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hzcomm x hxP
  have hDexp : ∀ d ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z, d ^ p = 1 := fun d hd =>
    (isElemAbelian_sup_zpowers (isElemAbelian_zpowers hxp) hxz' hzp).2 d hd
  have hzx : z ∈ Subgroup.zpowers x :=
    mem_zpowers_of_card_sup_le hp hxp hx1 (card_le_of_isCyclic_of_pow hp hDcyc hDexp)
  have heq : Subgroup.zpowers z = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzx)
      (by rw [card_zpowers_eq_of_pow hp hxp hx1, card_zpowers_eq_of_pow hp hzp hz1])
  have hxz : x ∈ Subgroup.zpowers z := heq ▸ Subgroup.mem_zpowers x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxz
  have hPC : P ≤ Subgroup.centralizer ({x} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff, ← hk]
    exact (Commute.zpow_left (show Commute z g from (hzcomm g hg).symm) k).eq.symm
  rw [inf_eq_left.2 hPC] at hcyc
  exact hcyc

theorem isCyclic_of_forall_isCyclic_inf_centralizer {p : ℕ} (hp : p.Prime) {Z : Subgroup G}
    {x : G} (hxZ : x ∈ Z) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (key : ∀ S : Subgroup G, S ≤ Subgroup.centralizer ({x} : Set G) ⊓ Z → IsPGroup p S →
      IsCyclic S)
    {S : Subgroup G} (hSZ : S ≤ Z) (hS : IsPGroup p S) : IsCyclic S := by
  have : Fact p.Prime := ⟨hp⟩
  have hzp : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [pow_one]; exact card_zpowers_eq_of_pow hp hxp hx1)
  obtain ⟨P, hxP, hPZ, hPp, hPi⟩ := exists_sylow_ge hp (Subgroup.zpowers_le.2 hxZ) hzp
  obtain ⟨w, -, hw⟩ := exists_conj_mem_of_sylow hp hSZ hS hPp hPi
  have hPcyc : IsCyclic P :=
    isCyclic_of_inf_centralizer hp hPp (hxP (Subgroup.mem_zpowers x)) hx1 hxp
      (key _ (fun g hg => ⟨hg.2, hPZ hg.1⟩) hPp.to_inf_left)
  exact isCyclic_of_forall_conj_mem hPcyc w hw

theorem isElemAbelian_card_sup_zpowers {p : ℕ} (hp : p.Prime) {a b : G} (hab : a * b = b * a)
    (ha : a ^ p = 1) (hb : b ^ p = 1) (hb1 : b ≠ 1) (hna : a ∉ Subgroup.zpowers b) :
    IsElemAbelian p (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ∧
      Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) = p ^ 2 := by
  have ha1 : a ≠ 1 := fun h => hna (h ▸ Subgroup.one_mem _)
  have hBb : Subgroup.zpowers a ≤ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hab
  refine ⟨isElemAbelian_sup_zpowers (isElemAbelian_zpowers ha) hBb hb, ?_⟩
  have hnorm : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_zpowers_of_comm hab
  have h1 := card_sup_mul_card_inf_of_le_normalizer hnorm
  have hcb := card_zpowers_eq_of_pow hp hb hb1
  have hca := card_zpowers_eq_of_pow hp ha ha1
  have hI : Nat.card (Subgroup.zpowers b ⊓ Subgroup.zpowers a : Subgroup G) = 1 := by
    have hd : Nat.card (Subgroup.zpowers b ⊓ Subgroup.zpowers a : Subgroup G) ∣ p := by
      rw [← hcb]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hd with h | h
    · exact h
    · exfalso
      have e1 : Subgroup.zpowers b ⊓ Subgroup.zpowers a = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hcb])
      have e2 : Subgroup.zpowers b ⊓ Subgroup.zpowers a = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hca])
      apply hna
      rw [e1.symm.trans e2]
      exact Subgroup.mem_zpowers a
  rw [hI, hcb, hca, mul_one] at h1
  rw [sup_comm, h1]
  ring

theorem mem_normalizer_zpowers_sup {a b g : G}
    (ha : g * a * g⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (hb : g * b * g⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conj_mem
  set V := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hV
  set K' := V.comap (MulAut.conj g).toMonoidHom with hK'
  have hmem : ∀ y, y ∈ K' ↔ g * y * g⁻¹ ∈ V := fun y => by
    simp [hK', MulAut.conj_apply]
  have hle : V ≤ K' :=
    sup_le (Subgroup.zpowers_le.2 ((hmem a).2 ha)) (Subgroup.zpowers_le.2 ((hmem b).2 hb))
  intro y hy
  exact (hmem y).1 (hle hy)

end Finite

end Prop53

end CFSG.LocalAnalysis.GLTheoremA
