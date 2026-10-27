module

public import CFSG.GH74.E2.LocalComp
public import CFSG.GH74.E2.K0Simple
public import CFSG.GH74.E2.Action
public import CFSG.GH74.E2.ComponentsBridge
public import CFSG.LocalAnalysis.ComponentInitial.StandardCriterion
public import CFSG.GH74.E2.FrattiniRank

public section

namespace CFSG.GH74.E2.NoM12

open Subgroup

theorem isCyclic_of_rank_le_one {X : Type*} [Group X] [Finite X] (h : Group.rank X ≤ 1) :
    IsCyclic X := by
  obtain ⟨S, hS, hcl⟩ := Group.rank_spec (G := X)
  have hcard : S.card ≤ 1 := hS ▸ h
  obtain ⟨g, hg⟩ := Finset.card_le_one_iff_subset_singleton.1 hcard
  have hle : Subgroup.closure (S : Set X) ≤ Subgroup.zpowers g := by
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_mono (by exact_mod_cast hg)
  rw [hcl, top_le_iff] at hle
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨g, hle⟩

theorem eq_of_orderOf_two_of_cyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {x y : C}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  classical
  have := Fintype.ofFinite C
  by_contra hne
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; omega
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy; omega
  have hsub : ({1, x, y} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact hx2
    · exact hy2
  have h3 : ({1, x, y} : Finset C).card = 3 :=
    Finset.card_eq_three.2 ⟨1, x, y, hx1.symm, hy1.symm, hne, rfl⟩
  have := (Finset.card_le_card hsub).trans (IsCyclic.card_pow_eq_one_le (α := C) (by norm_num : 0 < 2))
  omega


variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem' (P : Subgroup G) (σ : G)
    (h : ∀ x ∈ P, σ * x * σ⁻¹ ∈ P) : σ ∈ normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : P → P := fun y => ⟨σ * y * σ⁻¹, h y y.2⟩
  have hinj : Function.Injective f := by
    intro y z hyz
    have := congrArg Subtype.val hyz
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨σ * x * σ⁻¹, hx⟩
  have := congrArg Subtype.val hy
  simp only [f, mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact y.2

theorem conj_eq_of_odd_order {Q : Subgroup G} [IsCyclic Q] (hQ : IsPGroup 2 Q) {x : G}
    (hx : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hodd : Odd (orderOf x)) : ∀ q ∈ Q, x * q * x⁻¹ = q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxN : x ∈ normalizer (Q : Set G) := mem_normalizer_of_conj_mem' Q x hx
  set σ : MulAut Q := Q.normalizerMonoidHom ⟨x, hxN⟩ with hσ
  have hσq : ∀ q : Q, ((σ q : Q) : G) = x * q * x⁻¹ := fun q => rfl
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  have h1 : orderOf σ ∣ orderOf x := by
    have := orderOf_map_dvd Q.normalizerMonoidHom (⟨x, hxN⟩ : normalizer (Q : Set G))
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf σ ∣ 2 ^ k := by
    have h := orderOf_dvd_natCard σ
    rw [IsCyclic.card_mulAut, hk] at h
    refine h.trans ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · rw [Nat.totient_prime_pow Nat.prime_two hk0]
      simpa using pow_dvd_pow 2 (Nat.sub_le k 1)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hodd' : Odd (orderOf σ) := Odd.of_dvd_nat hodd h1
  have hσ1 : σ = 1 := by
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rw [pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    · exfalso
      rw [hj] at hodd'
      exact (Nat.not_even_iff_odd.mpr hodd') (even_two.pow_of_ne_zero hjpos.ne')
  intro q hq
  have := hσq ⟨q, hq⟩
  rw [hσ1] at this
  simpa using this.symm


section Local

theorem rank_qt_le_one (hH : Hyp G) {w : G} (hw : orderOf w = 2)
    (huniq : ∀ K₁ K₂ : Subgroup G, IsCompCen w K₁ → IsCompCen w K₂ → K₁ = K₂)
    {K : Subgroup G} (hK : IsCompCen w K) (hsh : Shape2M12 ↥K) : Group.rank ↥(Qt w) ≤ 1 := by
  have hLoc := localK_of_component hH hw huniq hK
  obtain ⟨U, hU2, hU4⟩ := rank_ge4_of_shape2M12 hsh
  set U' : Subgroup G := U.map K.subtype with hU'def
  have hU'2 : IsPGroup 2 ↥U' := hU2.map K.subtype
  have hrU' : Group.rank ↥U' = Group.rank ↥U :=
    (Group.rank_congr (U.equivMapOfInjective K.subtype K.subtype_injective)).symm
  have hU'K : U' ≤ K := Subgroup.map_subtype_le U
  have hcomm : ∀ q ∈ Qt w, ∀ u ∈ U', q * u = u * q := by
    intro q hq u hu
    obtain ⟨hqC, hqQ⟩ := mem_Qt.1 hq
    have huK : u ∈ K := hU'K hu
    have h1 := hLoc.commute ⟨q, hqC⟩ hqQ ⟨u, hK.1 huK⟩ (Subgroup.mem_subgroupOf.2 huK)
    exact congrArg Subtype.val h1
  have h1 := gen4_rank_add_le hH.gen4 (Qt w) U' (Qt_isPGroup w) hU'2 hcomm
  have hle : Qt w ⊓ U' ≤ (center ↥K).map K.subtype := by
    rintro x ⟨hxQ, hxU⟩
    have hxK : x ∈ K := hU'K hxU
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    obtain ⟨hxC, hxQ'⟩ := mem_Qt.1 hxQ
    have h2 := hLoc.commute ⟨x, hxC⟩ hxQ' ⟨g.1, hK.1 g.2⟩ (Subgroup.mem_subgroupOf.2 g.2)
    exact (congrArg Subtype.val h2).symm
  have hcard : Nat.card ↥(Qt w ⊓ U') ≤ 2 := by
    calc Nat.card ↥(Qt w ⊓ U') ≤ Nat.card ↥((center ↥K).map K.subtype) :=
          Subgroup.card_le_of_le hle
      _ = Nat.card ↥(center ↥K) := Subgroup.card_map_of_injective K.subtype_injective
      _ = 2 := hsh.2.1
  have h3 := rank_le_one_of_card_le_two hcard
  omega

theorem center_le_qt (hH : Hyp G) {w : G} (hw : orderOf w = 2)
    (huniq : ∀ K₁ K₂ : Subgroup G, IsCompCen w K₁ → IsCompCen w K₂ → K₁ = K₂)
    {K : Subgroup G} (hK : IsCompCen w K) :
    ∀ z : ↥K, z ∈ center ↥K → ((z : ↥K) : G) ∈ Qt w := by
  intro z hz
  have hLoc := localK_of_component hH hw huniq hK
  let zh : ↥(Cen w) := ⟨(z : G), hK.1 z.2⟩
  have hzhK : zh ∈ K.subgroupOf (Cen w) := Subgroup.mem_subgroupOf.2 z.2
  have hzhQ : zh ∈ CFSG.pCore 2 ↥(Cen w) := by
    refine hLoc.self_centralizing zh (fun q hq => (hLoc.commute q hq zh hzhK).symm) (fun k hk => ?_)
    have hk' : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
    have h1 := Subgroup.mem_center_iff.1 hz ⟨(k : G), hk'⟩
    apply Subtype.ext
    exact (congrArg Subtype.val h1).symm
  exact mem_Qt.2 ⟨zh.2, hzhQ⟩

theorem w_mem_K (hH : Hyp G) {w : G} (hw : orderOf w = 2)
    (huniq : ∀ K₁ K₂ : Subgroup G, IsCompCen w K₁ → IsCompCen w K₂ → K₁ = K₂)
    {K : Subgroup G} (hK : IsCompCen w K) (hsh : Shape2M12 ↥K) : w ∈ K := by
  have hcyc : IsCyclic ↥(Qt w) := isCyclic_of_rank_le_one (rank_qt_le_one hH hw huniq hK hsh)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥K)) 2 (by rw [hsh.2.1])
  have hzQ : ((z : ↥K) : G) ∈ Qt w := center_le_qt hH hw huniq hK (z : ↥K) z.2
  have hz2 : orderOf (((z : ↥K) : G)) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hwQ : w ∈ Qt w := t_mem_Qt hw
  have heq := eq_of_orderOf_two_of_cyclic (C := ↥(Qt w)) (x := ⟨w, hwQ⟩)
    (y := ⟨((z : ↥K) : G), hzQ⟩) (by rw [Subgroup.orderOf_mk]; exact hw)
    (by rw [Subgroup.orderOf_mk]; exact hz2)
  have hwz : w = ((z : ↥K) : G) := congrArg Subtype.val heq
  rw [hwz]
  exact (z : ↥K).2


theorem centralizer_le_qt (hH : Hyp G) {w : G} (hw : orderOf w = 2)
    (huniq : ∀ K₁ K₂ : Subgroup G, IsCompCen w K₁ → IsCompCen w K₂ → K₁ = K₂)
    {K : Subgroup G} (hK : IsCompCen w K) (hsh : Shape2M12 ↥K) :
    centralizer (K : Set G) ≤ Qt w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLoc := localK_of_component hH hw huniq hK
  have hwK := w_mem_K hH hw huniq hK hsh
  have hcyc : IsCyclic ↥(Qt w) := isCyclic_of_rank_le_one (rank_qt_le_one hH hw huniq hK hsh)
  set N : Subgroup G := centralizer (K : Set G) with hN
  have hNC : N ≤ Cen w := fun n hn => mem_Cen.2 (mem_centralizer_iff.1 hn w hwK)
  have h2elem : ∀ x ∈ N, ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
    intro x hx
    have hxC : x ∈ Cen w := hNC hx
    obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    set y := x ^ (2 ^ k) with hy
    have hyN : y ∈ N := N.pow_mem hx _
    have hyC : y ∈ Cen w := hNC hyN
    have hyord : orderOf y = m := by
      rw [hy, orderOf_pow_of_dvd (by positivity) ⟨m, hn⟩]
      rw [hn]
      exact Nat.mul_div_cancel_left m (by positivity)
    have hyodd : Odd (orderOf y) := hyord ▸ hm
    have hcommQ : ∀ q ∈ Qt w, y * q * y⁻¹ = q :=
      conj_eq_of_odd_order (Q := Qt w) (Qt_isPGroup w) (fun q hq => Qt_conj_mem w hyC hq) hyodd
    have hyQ : y ∈ Qt w := by
      refine mem_Qt.2 ⟨hyC, hLoc.self_centralizing ⟨y, hyC⟩ (fun q hq => ?_) (fun kk hkk => ?_)⟩
      · have hqQ : (q : G) ∈ Qt w := mem_Qt.2 ⟨q.2, hq⟩
        have h1 := hcommQ q hqQ
        apply Subtype.ext
        change y * (q : G) = (q : G) * y
        calc y * (q : G) = y * q * y⁻¹ * y := by group
          _ = q * y := by rw [h1]
      · have hkk' : (kk : G) ∈ K := Subgroup.mem_subgroupOf.1 hkk
        apply Subtype.ext
        exact (mem_centralizer_iff.1 hyN (kk : G) hkk').symm
    have hmem := (IsPGroup.iff_orderOf.1 (Qt_isPGroup w)) ⟨y, hyQ⟩
    obtain ⟨j, hj⟩ := hmem
    rw [Subgroup.orderOf_mk, hyord] at hj
    have hm1 : m = 1 := by
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simpa using hj
      · exfalso
        rw [hj] at hm
        exact (Nat.not_even_iff_odd.mpr hm) (even_two.pow_of_ne_zero hjpos.ne')
    have hy1 : y = 1 := by rw [← orderOf_eq_one_iff, hyord, hm1]
    exact ⟨k, hy1⟩
  let N' : Subgroup ↥(Cen w) := N.subgroupOf (Cen w)
  have hN'normal : N'.Normal := by
    refine ⟨fun n hn c => ?_⟩
    have hn' : ∀ k ∈ K, k * (n : G) = (n : G) * k := fun k hk =>
      mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hn) k hk
    rw [Subgroup.mem_subgroupOf, mem_centralizer_iff]
    intro k hk
    have hkC : k ∈ Cen w := hK.1 hk
    have hconj := hLoc.K_normal.conj_mem ⟨k, hkC⟩ (Subgroup.mem_subgroupOf.2 hk) c⁻¹
    have hk' : (c : G)⁻¹ * k * (c : G) ∈ K := by
      have := Subgroup.mem_subgroupOf.1 hconj
      simpa using this
    have h1 := hn' _ hk'
    change k * ((c : G) * (n : G) * (c : G)⁻¹) = (c : G) * (n : G) * (c : G)⁻¹ * k
    calc k * ((c : G) * (n : G) * (c : G)⁻¹)
        = (c : G) * (((c : G)⁻¹ * k * (c : G)) * (n : G)) * (c : G)⁻¹ := by group
      _ = (c : G) * ((n : G) * ((c : G)⁻¹ * k * (c : G))) * (c : G)⁻¹ := by rw [h1]
      _ = (c : G) * (n : G) * (c : G)⁻¹ * k := by group
  have hN'p : IsPGroup 2 ↥N' := by
    intro g
    obtain ⟨k, hk⟩ := h2elem (g : ↥(Cen w)).1 (Subgroup.mem_subgroupOf.1 g.2)
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun x : G => x) hk
    simpa using this
  have hN'le : N' ≤ CFSG.pCore 2 ↥(Cen w) := le_sSup ⟨hN'normal, hN'p⟩
  intro n hn
  exact mem_Qt.2 ⟨hNC hn, hN'le (Subgroup.mem_subgroupOf.2 hn)⟩


theorem isCyclic_centralizer (hH : Hyp G) {w : G} (hw : orderOf w = 2)
    (huniq : ∀ K₁ K₂ : Subgroup G, IsCompCen w K₁ → IsCompCen w K₂ → K₁ = K₂)
    {K : Subgroup G} (hK : IsCompCen w K) (hsh : Shape2M12 ↥K) :
    IsCyclic ↥(centralizer (K : Set G)) := by
  have hcyc : IsCyclic ↥(Qt w) := isCyclic_of_rank_le_one (rank_qt_le_one hH hw huniq hK hsh)
  exact Subgroup.isCyclic_of_le (centralizer_le_qt hH hw huniq hK hsh)

theorem isStandardSubgroup (hH : Hyp G) {w : G} (hw : orderOf w = 2)
    (huniq : ∀ K₁ K₂ : Subgroup G, IsCompCen w K₁ → IsCompCen w K₂ → K₁ = K₂)
    {K : Subgroup G} (hK : IsCompCen w K) (hsh : Shape2M12 ↥K) :
    CFSG.Assembly.ComponentType.IsStandardSubgroup K := by
  have hLoc := localK_of_component hH hw huniq hK
  have hwK := w_mem_K hH hw huniq hK hsh
  have hcyc : IsCyclic ↥(Qt w) := isCyclic_of_rank_le_one (rank_qt_le_one hH hw huniq hK hsh)
  have hle := centralizer_le_qt hH hw huniq hK hsh
  have hqs := isCompCen_quasisimple hK
  have hq : CFSG.Assembly.IsQuasisimple ↥K := ⟨Group.isPerfect_def.1 hqs.1, hqs.2.1⟩
  have hwC : w ∈ centralizer (K : Set G) := by
    rw [mem_centralizer_iff]
    intro k hk
    exact (mem_Cen.1 (hK.1 hk)).symm
  have heven : Even (Nat.card ↥(centralizer (K : Set G))) := by
    rw [even_iff_two_dvd]
    have h := orderOf_dvd_natCard (⟨w, hwC⟩ : ↥(centralizer (K : Set G)))
    rwa [Subgroup.orderOf_mk, hw] at h
  have hnonab : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hqs.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨a', a'.2, b', b'.2, fun h => hab ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext h
  have hLg : ∀ g : G, ⁅K, K.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
    intro g hg
    rw [Subgroup.commutator_comm] at hg
    have hle' := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hg
    obtain ⟨a, ha, b, hb, hab⟩ := hnonab
    have h1 : g * a * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := ⟨a, ha, rfl⟩
    have h2 : g * b * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := ⟨b, hb, rfl⟩
    have h3 := hle (hle' h1)
    have h4 := hle (hle' h2)
    have hcomm : (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹) := by
      have := (inferInstance : IsCyclic ↥(Qt w))
      have hc := (IsCyclic.commGroup (α := ↥(Qt w))).mul_comm ⟨_, h3⟩ ⟨_, h4⟩
      exact congrArg Subtype.val hc
    apply hab
    have h5 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) := hcomm
        _ = g * (b * a) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h5)
  refine (CFSG.LocalAnalysis.ComponentInitial.involution_component_standard_criterion hq heven
    hLg).2 ?_
  intro t ht ht2
  have htQ : t ∈ Qt w := hle ht
  have hwQ : w ∈ Qt w := t_mem_Qt hw
  have htw : t = w := by
    have := eq_of_orderOf_two_of_cyclic (C := ↥(Qt w)) (x := ⟨t, htQ⟩) (y := ⟨w, hwQ⟩)
      (by rw [Subgroup.orderOf_mk]; exact ht2) (by rw [Subgroup.orderOf_mk]; exact hw)
    exact congrArg Subtype.val this
  rw [htw]
  exact ⟨hK.1, CFSG.Assembly.IsSubnormal.step hK.1 hLoc.K_normal (CFSG.Assembly.IsSubnormal.refl _),
    hq⟩

end Local

end CFSG.GH74.E2.NoM12
