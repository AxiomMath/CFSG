module

public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.SelfCentralizingFour

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup

namespace TwoGroup

open CFSG.Open Subgroup

variable {P : Type*} [Group P] [Finite P]

omit [Finite P] in
theorem conjNormal_ker {H : Subgroup P} [H.Normal] :
    (MulAut.conjNormal (H := H)).ker = centralizer (H : Set P) := by
  ext q
  rw [MonoidHom.mem_ker, mem_centralizer_iff]
  constructor
  · intro hq h hh
    have heval := congrArg (fun a : MulAut H => (a ⟨h, hh⟩ : P)) hq
    have hconj : q * h * q⁻¹ = h := heval
    calc h * q = (q * h * q⁻¹) * q := by rw [hconj]
      _ = q * h := by group
  · intro hq
    ext h
    change q * (h : P) * q⁻¹ = h
    rw [← hq h h.2, mul_inv_cancel_right]

theorem selfCentralizing_rel (hP : IsPGroup 2 P) {S H : Subgroup P} [S.Normal] [H.Normal]
    (hHS : H ≤ S) (hHab : IsMulCommutative H)
    (hmax : ∀ B : Subgroup P, B ≤ S → B.Normal → IsMulCommutative B → H ≤ B → B ≤ H) :
    S ⊓ centralizer (H : Set P) ≤ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := S ⊓ centralizer (H : Set P) with hC
  by_contra hCH
  let q := QuotientGroup.mk' H
  have hCbar : C.map q ≠ ⊥ := by
    intro hbot
    apply hCH
    have hle := (Subgroup.map_eq_bot_iff C).mp hbot
    rwa [QuotientGroup.ker_mk'] at hle
  have : (C.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective H)
  have hnil : Group.IsNilpotent (P ⧸ H) := (hP.to_quotient H).isNilpotent
  have hmeet := Group.IsNilpotent.inf_center_ne_bot_of_normal hCbar
  obtain ⟨⟨xb, hxb⟩, hxb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hmeet
  obtain ⟨hxC, hxZ⟩ := mem_inf.1 hxb
  obtain ⟨x, hxCC, hxq⟩ := hxC
  set B := (zpowers (q x)).comap q with hB
  have hBn : B.Normal := by
    have : (zpowers (q x)).Normal := normal_of_le_center (zpowers_le.2 (hxq ▸ hxZ))
    exact Normal.comap this q
  have hHB : H ≤ B := by
    intro h hh
    have h1 : q h = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff h).2 hh
    change q h ∈ zpowers (q x)
    rw [h1]
    exact one_mem _
  have hform : ∀ b ∈ B, ∃ k : ℤ, ∃ h ∈ H, b = x ^ k * h := by
    intro b hb
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (show q b ∈ zpowers (q x) from hb)
    refine ⟨k, (x ^ k)⁻¹ * b, ?_, by group⟩
    rw [← QuotientGroup.ker_mk' H, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hk,
      inv_mul_cancel]
  have hxS : x ∈ S := (mem_inf.1 hxCC).1
  have hxcen : ∀ h ∈ H, x * h = h * x := fun h hh =>
    ((mem_centralizer_iff.1 (mem_inf.1 hxCC).2) h hh).symm
  have hBS : B ≤ S := by
    intro b hb
    obtain ⟨k, h, hh, rfl⟩ := hform b hb
    exact mul_mem (zpow_mem hxS k) (hHS hh)
  have hBab : IsMulCommutative B := by
    refine ⟨⟨fun b₁ b₂ => Subtype.ext ?_⟩⟩
    obtain ⟨k₁, h₁, hh₁, he₁⟩ := hform b₁ b₁.2
    obtain ⟨k₂, h₂, hh₂, he₂⟩ := hform b₂ b₂.2
    have hxk : ∀ (k : ℤ), ∀ h ∈ H, x ^ k * h = h * x ^ k := by
      intro k h hh
      exact ((Commute.zpow_left (hxcen h hh) k)).eq
    have hh12 : h₁ * h₂ = h₂ * h₁ := by
      have := isMulCommutative_iff.mp hHab ⟨h₁, hh₁⟩ ⟨h₂, hh₂⟩
      exact congrArg (fun w : H => (w : P)) this
    change (b₁ : P) * b₂ = b₂ * b₁
    rw [he₁, he₂]
    calc x ^ k₁ * h₁ * (x ^ k₂ * h₂) = x ^ k₁ * (h₁ * x ^ k₂) * h₂ := by group
      _ = x ^ k₁ * (x ^ k₂ * h₁) * h₂ := by rw [hxk k₂ h₁ hh₁]
      _ = x ^ k₂ * x ^ k₁ * (h₁ * h₂) := by
          rw [(Commute.zpow_zpow_self x k₂ k₁).eq]
          group
      _ = x ^ k₂ * x ^ k₁ * (h₂ * h₁) := by rw [hh12]
      _ = x ^ k₂ * (x ^ k₁ * h₂) * h₁ := by group
      _ = x ^ k₂ * (h₂ * x ^ k₁) * h₁ := by rw [hxk k₁ h₂ hh₂]
      _ = x ^ k₂ * h₂ * (x ^ k₁ * h₁) := by group
  have hBH := hmax B hBS hBn hBab hHB
  apply hxb1
  have hxB : x ∈ B := by
    change q x ∈ zpowers (q x)
    exact mem_zpowers _
  have : q x = 1 := (QuotientGroup.eq_one_iff x).2 (hBH hxB)
  apply Subtype.ext
  change xb = 1
  rw [← hxq]
  exact this

theorem cyclic_normal_index_two_rel (hP : IsPGroup 2 P) (S : Subgroup P) [S.Normal]
    (hcyc : ∀ B : Subgroup P, B ≤ S → B.Normal → IsMulCommutative B → IsCyclic B) :
    ∃ H : Subgroup P, H ≤ S ∧ H.Normal ∧ IsCyclic H ∧ (H.subgroupOf S).index ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup P) :=
    Finite.of_injective (fun H : Subgroup P => (H : Set P)) SetLike.coe_injective
  obtain ⟨H, -, hHmax⟩ := (Set.toFinite
      {A : Subgroup P | A ≤ S ∧ A.Normal ∧ IsMulCommutative A}).exists_le_maximal
    (a := ⊥) ⟨bot_le, inferInstance, inferInstance⟩
  obtain ⟨hHS, hHn, hHab⟩ := hHmax.1
  have hHcyc : IsCyclic H := hcyc H hHS hHn hHab
  refine ⟨H, hHS, hHn, hHcyc, ?_⟩
  have hcent : S ⊓ centralizer (H : Set P) ≤ H :=
    selfCentralizing_rel hP hHS hHab (fun B hBS hBn hBab hHB => hHmax.2 ⟨hBS, hBn, hBab⟩ hHB)
  by_contra hidx
  push Not at hidx
  let ψ : P →* MulAut H := MulAut.conjNormal
  let φ : S →* MulAut H := ψ.comp S.subtype
  have hker : φ.ker = H.subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change ψ s = 1 ↔ _
    rw [← MonoidHom.mem_ker, conjNormal_ker]
    constructor
    · intro hs
      exact hcent (mem_inf.2 ⟨s.2, hs⟩)
    · intro hs
      rw [mem_centralizer_iff]
      intro h hh
      exact congrArg (fun w : H => (w : P)) (isMulCommutative_iff.mp hHab ⟨h, hh⟩ ⟨s, hs⟩)
  have hΓ : 2 < Nat.card φ.range := by
    rw [← Subgroup.index_ker, hker]
    exact hidx
  obtain ⟨h₀, hh₀⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).mp hHcyc
  have hh₀H : h₀ ∈ H := hh₀ ▸ Subgroup.mem_zpowers h₀
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hP.to_subgroup H)
  have hord : orderOf h₀ = 2 ^ a := by rw [← Nat.card_zpowers, hh₀, ha]
  let hH : H := ⟨h₀, hh₀H⟩
  have hordH : orderOf hH = 2 ^ a := by rw [Subgroup.orderOf_mk]; exact hord
  have hgen : Subgroup.zpowers hH = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, hordH, ha]
  have ha3 : 3 ≤ a := by
    by_contra hlt
    push Not at hlt
    have : Finite (MulAut H) :=
      Finite.of_injective (fun σ : MulAut H => (σ : H → H)) (fun σ τ hστ => MulEquiv.ext
        (congrFun hστ))
    have h1 : Nat.card φ.range ≤ Nat.card (MulAut H) := Subgroup.card_le_card_group _
    rw [IsCyclic.card_mulAut, ha] at h1
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      rw [pow_zero, Nat.totient_one] at h1
      omega
    · rw [Nat.totient_prime_pow Nat.prime_two hpos, show (2 : ℕ) - 1 = 1 from rfl,
        mul_one] at h1
      have : 2 ^ (a - 1) ≤ 2 := by
        calc 2 ^ (a - 1) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 2 := by norm_num
      omega
  obtain ⟨σ, hσΓ, hσh, hσord⟩ :=
    RankTwoShapes.cyclic_two_large_automorphism_subgroup ha3 hH hgen hordH φ.range hΓ
  obtain ⟨g, rfl⟩ := hσΓ
  have hgh : (g : P) * h₀ * (g : P)⁻¹ = h₀ ^ (1 + 2 ^ (a - 1)) := by
    have := congrArg Subtype.val hσh
    simpa [φ, ψ, MulAut.conjNormal_apply, hH] using this
  have hgH : (g : P) ∉ H := by
    intro hg
    have h1 : φ g = 1 := by
      rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
      exact hg
    rw [h1, orderOf_one] at hσord
    norm_num at hσord
  have hg2 : (g : P) ^ 2 ∈ H := by
    have : g ^ 2 ∈ H.subgroupOf S := by
      rw [← hker, MonoidHom.mem_ker, map_pow, ← hσord, pow_orderOf_eq_one]
    rw [mem_subgroupOf] at this
    simpa using this
  have hHz : ∀ k ∈ H, k ∈ Subgroup.zpowers h₀ := fun k hk => hh₀ ▸ hk
  obtain ⟨c, hy2, hout, hin⟩ :=
    RankTwoShapes.unipotent_extension_involutions ha3 hord (hHz _ hg2) hgh
  set z := h₀ ^ 2 ^ (a - 1) with hz
  set y := h₀ ^ c * (g : P) with hy
  have hzH : z ∈ H := H.pow_mem hh₀H _
  have hyS : y ∈ S := S.mul_mem (hHS (H.pow_mem hh₀H c)) g.2
  have hyH : y ∉ H := fun hmem => hgH (by
    have e : (g : P) = (h₀ ^ c)⁻¹ * y := by rw [hy, inv_mul_cancel_left]
    rw [e]
    exact H.mul_mem (H.inv_mem (H.pow_mem hh₀H c)) hmem)
  have hz1 : z ≠ 1 := pow_ne_one_of_lt_orderOf (pow_ne_zero _ two_ne_zero)
    (by rw [hord]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hz2 : z ^ 2 = 1 := by
    rw [hz, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ a), ← hord,
      pow_orderOf_eq_one]
  have hconjz : ∀ p : P, p * z * p⁻¹ = z := by
    intro p
    have hmem : p * z * p⁻¹ ∈ H := hHn.conj_mem z hzH p
    have hsq : (p * z * p⁻¹) ^ 2 = 1 := by rw [conj_pow, hz2]; group
    rcases hin _ (hHz _ hmem) hsq with h1 | h1
    · exfalso
      apply hz1
      calc z = p⁻¹ * (p * z * p⁻¹) * p := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  have hcommAut : ∀ p : P, p * (g : P) * p⁻¹ * (g : P)⁻¹ ∈ H := by
    intro p
    apply hcent
    refine mem_inf.2 ⟨?_, ?_⟩
    · exact S.mul_mem (‹S.Normal›.conj_mem _ g.2 p) (S.inv_mem g.2)
    · rw [← conjNormal_ker, MonoidHom.mem_ker]
      change ψ (p * (g : P) * p⁻¹ * (g : P)⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv,
        RankTwoShapes.mulAut_mul_comm_of_isCyclic (ψ p) (ψ g)]
      group
  have hconjy : ∀ p : P, p * y * p⁻¹ = y ∨ p * y * p⁻¹ = z * y := by
    intro p
    obtain ⟨w, hw⟩ : ∃ w, w = p * y * p⁻¹ * y⁻¹ := ⟨_, rfl⟩
    have hwH : w ∈ H := by
      have e : w = (p * h₀ ^ c * p⁻¹) * (p * (g : P) * p⁻¹ * (g : P)⁻¹) * (h₀ ^ c)⁻¹ := by
        rw [hw, hy]
        group
      rw [e]
      exact H.mul_mem (H.mul_mem (hHn.conj_mem _ (H.pow_mem hh₀H c) p) (hcommAut p))
        (H.inv_mem (H.pow_mem hh₀H c))
    have e2 : p * y * p⁻¹ = w * y := by rw [hw, inv_mul_cancel_right]
    have hsq : (w * y) ^ 2 = 1 := by
      rw [← e2, conj_pow, hy2]
      group
    rcases hout w (hHz w hwH) hsq with h1 | h1
    · left
      rw [e2, h1, one_mul]
    · right
      rw [e2, h1]
  have hzc : ∀ q : P, q * z = z * q := fun q => by
    calc q * z = q * z * q⁻¹ * q := by group
      _ = z * q := by rw [hconjz]
  set V := Subgroup.closure ({z, y} : Set P) with hV
  have hzV : z ∈ V := Subgroup.subset_closure (by simp)
  have hyV : y ∈ V := Subgroup.subset_closure (by simp)
  have hVn : V.Normal := by
    apply RankTwoShapes.closure_normal_of_conj_mem
    intro p k hk
    rcases hk with rfl | rfl
    · rw [hconjz]
      exact hzV
    · rcases hconjy p with h1 | h1 <;> rw [h1]
      · exact hyV
      · exact V.mul_mem hzV hyV
  have hVab : IsMulCommutative V := by
    rw [← Subgroup.le_centralizer_iff_isMulCommutative, hV, Subgroup.centralizer_closure,
      Subgroup.closure_le]
    intro k hk
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro l hl
    rcases hk with rfl | rfl
    · exact hzc l
    · rcases hl with rfl | rfl
      · exact (hzc y).symm
      · rfl
  have hVS : V ≤ S := by
    rw [hV, Subgroup.closure_le]
    rintro k (rfl | rfl)
    · exact hHS hzH
    · exact hyS
  have hVcyc : IsCyclic V := hcyc V hVS hVn hVab
  have heq := RankTwoShapes.eq_of_sq_eq_one_of_isCyclic (G := V) (a := ⟨z, hzV⟩) (b := ⟨y, hyV⟩)
    (Subtype.ext (by simpa using hz2)) (fun h1 => hz1 (congrArg Subtype.val h1))
    (Subtype.ext (by simpa using hy2))
    (fun h1 => hyH (by
      have e : y = 1 := congrArg Subtype.val h1
      rw [e]
      exact H.one_mem))
  have e : z = y := congrArg Subtype.val heq
  exact hyH (e ▸ hzH)

omit [Finite P] in
theorem involution_unique_of_isCyclic {H : Subgroup P} (hH : IsCyclic H) {a b : P} (ha : a ∈ H)
    (hb : b ∈ H) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) : a = b := by
  have := RankTwoShapes.eq_of_sq_eq_one_of_isCyclic (G := H) (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    (Subtype.ext (by simpa using ha2)) (fun h => ha1 (congrArg Subtype.val h))
    (Subtype.ext (by simpa using hb2)) (fun h => hb1 (congrArg Subtype.val h))
  exact congrArg Subtype.val this

theorem involution_structure_rel (hP : IsPGroup 2 P) (S : Subgroup P) [S.Normal]
    (hcyc : ∀ B : Subgroup P, B ≤ S → B.Normal → IsMulCommutative B → IsCyclic B)
    {x₁ x₂ : P} (hx₁ : x₁ ∈ S) (hx₂ : x₂ ∈ S) (ho₁ : x₁ ^ 2 = 1) (ho₂ : x₂ ^ 2 = 1)
    (h₁ : x₁ ≠ 1) (h₂ : x₂ ≠ 1) (hne : x₁ ≠ x₂) :
    ∃ H : Subgroup P, H ≤ S ∧ H.Normal ∧ IsCyclic H ∧ (H.subgroupOf S).index = 2 ∧
    ∃ t z : P, t ∈ S ∧ t ∉ H ∧ t ^ 2 = 1 ∧ z ∈ H ∧ z ^ 2 = 1 ∧ z ≠ 1 ∧
      ∀ h ∈ H, t * h = h * t → h = 1 ∨ h = z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, hHS, hHn, hHcyc, hind⟩ := cyclic_normal_index_two_rel hP S hcyc
  obtain ⟨t, htS, htH, ht2, ht1⟩ : ∃ t, t ∈ S ∧ t ∉ H ∧ t ^ 2 = 1 ∧ t ≠ 1 := by
    by_cases hx₁H : x₁ ∈ H
    · by_cases hx₂H : x₂ ∈ H
      · exact absurd (involution_unique_of_isCyclic hHcyc hx₁H hx₂H ho₁ h₁ ho₂ h₂) hne
      · exact ⟨x₂, hx₂, hx₂H, ho₂, h₂⟩
    · exact ⟨x₁, hx₁, hx₁H, ho₁, h₁⟩
  have hind2 : (H.subgroupOf S).index = 2 := by
    have hne1 : (H.subgroupOf S).index ≠ 1 := by
      intro h
      rw [Subgroup.index_eq_one] at h
      have : (⟨t, htS⟩ : S) ∈ H.subgroupOf S := h ▸ mem_top _
      exact htH this
    have hpos : (H.subgroupOf S).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hcoset : ∀ a ∈ S, ∀ b ∈ S, a ∉ H → b ∉ H → a * b ∈ H := by
    intro a ha b hb haH hbH
    have := (Subgroup.mul_mem_iff_of_index_two hind2 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).2
      (iff_of_false haH hbH)
    exact this
  have htinv : t⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hxx : x₁ * x₂ ∈ H := by
      apply hcoset x₁ hx₁ x₂ hx₂ <;> rw [hbot] <;> simpa
    rw [hbot, mem_bot] at hxx
    apply hne
    have hx₁inv : x₁⁻¹ = x₁ := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ho₁]
    calc x₁ = x₁⁻¹ := hx₁inv.symm
      _ = x₂ := (eq_inv_of_mul_eq_one_right hxx).symm
  have hHp : IsPGroup 2 H := hP.to_subgroup H
  have h2H : 2 ∣ Nat.card H := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hHp
    have : Nontrivial H := (nontrivial_iff_ne_bot H).2 hHne
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card).ne' hk
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨⟨z, hzH⟩, hzo⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 h2H
  have hzo' : orderOf z = 2 := by rw [← Subgroup.orderOf_mk z hzH]; exact hzo
  have hz2 : z ^ 2 = 1 := by rw [← hzo']; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzo'
    norm_num at hzo'
  refine ⟨H, hHS, hHn, hHcyc, hind2, t, z, htS, htH, ht2, hzH, hz2, hz1, ?_⟩
  have hzconj : ∀ p : P, p * z * p⁻¹ = z := by
    intro p
    apply involution_unique_of_isCyclic hHcyc (hHn.conj_mem z hzH p) hzH
      (by rw [conj_pow, hz2]; group) _ hz2 hz1
    intro h
    apply hz1
    calc z = p⁻¹ * (p * z * p⁻¹) * p := by group
      _ = 1 := by rw [h]; group
  let σ : H →* H := (MulAut.conjNormal (H := H) t).toMonoidHom
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ
  have hσ : ∀ k ∈ H, t * k * t⁻¹ = k ^ m := by
    intro k hk
    have := congrArg Subtype.val (hm ⟨k, hk⟩)
    simpa [σ, MulAut.conjNormal_apply] using this
  intro h hh hth
  by_contra hcon
  push Not at hcon
  obtain ⟨hh1, hhz⟩ := hcon
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hHp ⟨h, hh⟩
  rw [Subgroup.orderOf_mk] at hj
  have hj2 : 2 ≤ j := by
    by_contra hlt
    push Not at hlt
    interval_cases j
    · rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hh1 hj
    · have hh2 : h ^ 2 = 1 := by rw [pow_one] at hj; rw [← hj]; exact pow_orderOf_eq_one h
      exact hhz (involution_unique_of_isCyclic hHcyc hh hzH hh2 hh1 hz2 hz1)
  have hm1 : (4 : ℤ) ∣ m - 1 := by
    have hfix : h ^ (m - 1) = 1 := by
      have h1 : t * h * t⁻¹ = h := by rw [hth, mul_inv_cancel_right]
      rw [hσ h hh] at h1
      rw [zpow_sub, zpow_one, h1, mul_inv_cancel]
    have hdvd := orderOf_dvd_iff_zpow_eq_one.2 hfix
    rw [hj] at hdvd
    have h4 : (4 : ℤ) ∣ ((2 ^ j : ℕ) : ℤ) := by
      have : (4 : ℕ) ∣ 2 ^ j := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ∣ 2 ^ j := pow_dvd_pow 2 hj2
      exact_mod_cast this
    exact h4.trans hdvd
  have hinvt : ∀ k ∈ H, (t * k) ^ 2 = 1 → k ^ 2 = 1 := by
    intro k hk hk2
    have hk' : k ^ (m + 1) = 1 := by
      have h1 : (t * k * t⁻¹) * k = 1 := by
        calc (t * k * t⁻¹) * k = (t * k) * (t * k) := by rw [htinv]; group
          _ = 1 := by rw [← pow_two]; exact hk2
      rw [hσ k hk] at h1
      rw [zpow_add, zpow_one]
      exact h1
    obtain ⟨i, hi⟩ := IsPGroup.iff_orderOf.mp hHp ⟨k, hk⟩
    rw [Subgroup.orderOf_mk] at hi
    have hdvd := orderOf_dvd_iff_zpow_eq_one.2 hk'
    rw [hi] at hdvd
    have hi1 : i ≤ 1 := by
      by_contra hlt
      push Not at hlt
      have h4 : (4 : ℤ) ∣ ((2 ^ i : ℕ) : ℤ) := by
        have : (4 : ℕ) ∣ 2 ^ i := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ∣ 2 ^ i := pow_dvd_pow 2 hlt
        exact_mod_cast this
      obtain ⟨c, hc⟩ := hm1
      obtain ⟨d, hd⟩ := h4.trans hdvd
      omega
    have : orderOf k ∣ 2 := by
      rw [hi]
      exact pow_dvd_pow 2 hi1 |>.trans (by norm_num)
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hinvS : ∀ s ∈ S, s ^ 2 = 1 → s ≠ 1 → s = z ∨ s = t ∨ s = t * z := by
    intro s hs hs2 hs1
    by_cases hsH : s ∈ H
    · exact Or.inl (involution_unique_of_isCyclic hHcyc hsH hzH hs2 hs1 hz2 hz1)
    · right
      have hk : t⁻¹ * s ∈ H := by
        rw [htinv]
        exact hcoset t htS s hs htH hsH
      have hk2 := hinvt _ hk (by rw [← mul_assoc, mul_inv_cancel, one_mul]; exact hs2)
      by_cases hk1 : t⁻¹ * s = 1
      · left
        calc s = t * (t⁻¹ * s) := by group
          _ = t := by rw [hk1, mul_one]
      · right
        have := involution_unique_of_isCyclic hHcyc hk hzH hk2 hk1 hz2 hz1
        calc s = t * (t⁻¹ * s) := by group
          _ = t * z := by rw [this]
  have htz : t * z = z * t := by
    calc t * z = t * z * t⁻¹ * t := by group
      _ = z * t := by rw [hzconj]
  set V := Subgroup.closure ({z, t} : Set P) with hV
  have hzV : z ∈ V := Subgroup.subset_closure (by simp)
  have htV : t ∈ V := Subgroup.subset_closure (by simp)
  have hVn : V.Normal := by
    apply RankTwoShapes.closure_normal_of_conj_mem
    intro p k hk
    rcases hk with rfl | rfl
    · rw [hzconj]
      exact hzV
    · have hpS : p * k * p⁻¹ ∈ S := ‹S.Normal›.conj_mem k htS p
      have hp2 : (p * k * p⁻¹) ^ 2 = 1 := by rw [conj_pow, ht2]; group
      have hp1 : p * k * p⁻¹ ≠ 1 := by
        intro h
        apply ht1
        calc k = p⁻¹ * (p * k * p⁻¹) * p := by group
          _ = 1 := by rw [h]; group
      rcases hinvS _ hpS hp2 hp1 with h | h | h <;> rw [h]
      · exact hzV
      · exact htV
      · exact V.mul_mem htV hzV
  have hVab : IsMulCommutative V := by
    rw [← Subgroup.le_centralizer_iff_isMulCommutative, hV, Subgroup.centralizer_closure,
      Subgroup.closure_le]
    intro k hk
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro l hl
    rcases hk with rfl | rfl <;> rcases hl with rfl | rfl
    · rfl
    · exact htz
    · exact htz.symm
    · rfl
  have hVS : V ≤ S := by
    rw [hV, Subgroup.closure_le]
    rintro k (rfl | rfl)
    · exact hHS hzH
    · exact htS
  have hVcyc : IsCyclic V := hcyc V hVS hVn hVab
  exact htH ((involution_unique_of_isCyclic hVcyc hzV htV hz2 hz1 ht2 ht1) ▸ hzH)

omit [Finite P] in
theorem centralizer_outside_rel {S H : Subgroup P} (hHcyc : IsCyclic H)
    (hind : (H.subgroupOf S).index = 2) {t z : P} (htS : t ∈ S) (htH : t ∉ H)
    (htc : ∀ h ∈ H, t * h = h * t → h = 1 ∨ h = z) :
    ∀ x ∈ S, x ∉ H → ∀ h ∈ H, x * h = h * x → h = 1 ∨ h = z := by
  intro x hxS hxH h hh hxh
  have hk : t⁻¹ * x ∈ H := by
    have := (Subgroup.mul_mem_iff_of_index_two hind (a := ⟨t⁻¹, S.inv_mem htS⟩)
      (b := ⟨x, hxS⟩)).2 (iff_of_false (fun h' => htH (by simpa using H.inv_mem h')) hxH)
    exact this
  have hkh : (t⁻¹ * x) * h = h * (t⁻¹ * x) := by
    have := isMulCommutative_iff.mp (hHcyc.isMulCommutative) ⟨t⁻¹ * x, hk⟩ ⟨h, hh⟩
    exact congrArg (fun w : H => (w : P)) this
  apply htc h hh
  calc t * h = x * (t⁻¹ * x)⁻¹ * h := by group
    _ = x * ((t⁻¹ * x)⁻¹ * h) := by group
    _ = x * (h * (t⁻¹ * x)⁻¹) := by
        congr 1
        calc (t⁻¹ * x)⁻¹ * h = (t⁻¹ * x)⁻¹ * (h * (t⁻¹ * x)) * (t⁻¹ * x)⁻¹ := by group
          _ = (t⁻¹ * x)⁻¹ * ((t⁻¹ * x) * h) * (t⁻¹ * x)⁻¹ := by rw [hkh]
          _ = h * (t⁻¹ * x)⁻¹ := by group
    _ = (x * h) * (t⁻¹ * x)⁻¹ := by group
    _ = (h * x) * (t⁻¹ * x)⁻¹ := by rw [hxh]
    _ = h * t := by group

omit [Finite P] in
theorem isCyclic_of_le_isCyclic {H Y : Subgroup P} (hH : IsCyclic H) (hYH : Y ≤ H) :
    IsCyclic Y :=
  (Subgroup.subgroupOfEquivOfLe hYH).isCyclic.1 inferInstance

omit [Finite P] in
theorem commuting_noncyclic_le {S H : Subgroup P} (hHcyc : IsCyclic H)
    (hind : (H.subgroupOf S).index = 2) {z : P}
    (hcent : ∀ x ∈ S, x ∉ H → ∀ h ∈ H, x * h = h * x → h = 1 ∨ h = z)
    {Y₁ Y₂ : Subgroup P} (hY₁ : Y₁ ≤ S) (hY₂ : Y₂ ≤ S) (hc₁ : ¬ IsCyclic Y₁)
    (hc₂ : ¬ IsCyclic Y₂) (hcomm : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, y₁ * y₂ = y₂ * y₁) : Y₂ ≤ Y₁ := by
  have hout : ∀ Y : Subgroup P, ¬ IsCyclic Y → ∃ x ∈ Y, x ∉ H := by
    intro Y hY
    by_contra hall
    push Not at hall
    exact hY (isCyclic_of_le_isCyclic hHcyc hall)
  obtain ⟨x₁, hx₁, hx₁H⟩ := hout Y₁ hc₁
  obtain ⟨x₂, hx₂, hx₂H⟩ := hout Y₂ hc₂
  have hcoset : ∀ a ∈ S, ∀ b ∈ S, a ∉ H → b ∉ H → a⁻¹ * b ∈ H := by
    intro a ha b hb haH hbH
    exact (Subgroup.mul_mem_iff_of_index_two hind (a := ⟨a⁻¹, S.inv_mem ha⟩)
      (b := ⟨b, hb⟩)).2 (iff_of_false (fun h' => haH (by simpa using H.inv_mem h')) hbH)
  have hzY₁ : z ∈ Y₁ := by
    by_contra hz
    apply hc₁
    have htriv : ∀ w ∈ Y₁, w ∈ H → w = 1 := by
      intro w hw hwH
      rcases hcent x₂ (hY₂ hx₂) hx₂H w hwH (hcomm w hw x₂ hx₂).symm with h | h
      · exact h
      · exact absurd (h ▸ hw) hz
    refine isCyclic_of_le_isCyclic (H := zpowers x₁) inferInstance ?_
    intro y hy
    by_cases hyH : y ∈ H
    · rw [htriv y hy hyH]
      exact one_mem _
    · have h1 := htriv _ (Y₁.mul_mem (Y₁.inv_mem hx₁) hy)
        (hcoset x₁ (hY₁ hx₁) y (hY₁ hy) hx₁H hyH)
      have : y = x₁ := by
        calc y = x₁ * (x₁⁻¹ * y) := by group
          _ = x₁ := by rw [h1, mul_one]
      rw [this]
      exact mem_zpowers x₁
  intro y hy
  by_cases hyH : y ∈ H
  · rcases hcent x₁ (hY₁ hx₁) hx₁H y hyH (hcomm x₁ hx₁ y hy) with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact hzY₁
  · have hk := hcoset x₁ (hY₁ hx₁) y (hY₂ hy) hx₁H hyH
    have hkc : x₁ * (x₁⁻¹ * y) = (x₁⁻¹ * y) * x₁ := by
      have := hcomm x₁ hx₁ y hy
      calc x₁ * (x₁⁻¹ * y) = y := by group
        _ = x₁⁻¹ * (x₁ * y) := by group
        _ = x₁⁻¹ * (y * x₁) := by rw [this]
        _ = (x₁⁻¹ * y) * x₁ := by group
    rcases hcent x₁ (hY₁ hx₁) hx₁H _ hk hkc with h | h
    · have : y = x₁ := by
        calc y = x₁ * (x₁⁻¹ * y) := by group
          _ = x₁ := by rw [h, mul_one]
      rw [this]
      exact hx₁
    · have : y = x₁ * z := by
        calc y = x₁ * (x₁⁻¹ * y) := by group
          _ = x₁ * z := by rw [h]
      rw [this]
      exact Y₁.mul_mem hx₁ hzY₁

theorem dihedral_or_semidihedral_rel (hP : IsPGroup 2 P) (S : Subgroup P) [S.Normal]
    (hcyc : ∀ B : Subgroup P, B ≤ S → B.Normal → IsMulCommutative B → IsCyclic B)
    {x₁ x₂ : P} (hx₁ : x₁ ∈ S) (hx₂ : x₂ ∈ S) (ho₁ : x₁ ^ 2 = 1) (ho₂ : x₂ ^ 2 = 1)
    (h₁ : x₁ ≠ 1) (h₂ : x₂ ≠ 1) (hne : x₁ ≠ x₂) :
    ((∃ n : ℕ, 2 ≤ n ∧ Nonempty (S ≃* DihedralGroup (2 ^ (n - 1)))) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nonempty (S ≃* SemidihedralGroup n))) ∧
    (∃ E : Subgroup P, E ≤ S ∧ IsMulCommutative E ∧ (∀ e ∈ E, e ^ 2 = 1) ∧ Nat.card E = 4) ∧
    ∀ Y₁ Y₂ : Subgroup P, Y₁ ≤ S → Y₂ ≤ S → ¬ IsCyclic Y₁ → ¬ IsCyclic Y₂ →
      (∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, y₁ * y₂ = y₂ * y₁) → Y₂ ≤ Y₁ := by
  classical
  obtain ⟨H, hHS, hHn, hHcyc, hind, t, z, htS, htH, ht2, hzH, hz2, hz1, htc⟩ :=
    involution_structure_rel hP S hcyc hx₁ hx₂ ho₁ ho₂ h₁ h₂ hne
  have hcent := centralizer_outside_rel hHcyc hind htS htH htc
  have hcmp := fun Y₁ Y₂ hY₁ hY₂ hc₁ hc₂ hcomm =>
    commuting_noncyclic_le (Y₁ := Y₁) (Y₂ := Y₂) hHcyc hind hcent hY₁ hY₂ hc₁ hc₂ hcomm
  have ht1 : t ≠ 1 := fun h => htH (h ▸ one_mem H)
  have htz : t * z = z * t := by
    have hsq : (t * z * t⁻¹) ^ 2 = 1 := by rw [conj_pow, hz2]; group
    have hmem : t * z * t⁻¹ ∈ H := hHn.conj_mem z hzH t
    have hne1 : t * z * t⁻¹ ≠ 1 := by
      intro h
      apply hz1
      calc z = t⁻¹ * (t * z * t⁻¹) * t := by group
        _ = 1 := by rw [h]; group
    have := involution_unique_of_isCyclic hHcyc hmem hzH hsq hne1 hz2 hz1
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [this]
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
  have hmemV : ∀ s : P, s ∈ S → (s * t = t * s ↔ s = 1 ∨ s = z ∨ s = t ∨ s = t * z) := by
    intro s hs
    constructor
    · intro hst
      by_cases hsH : s ∈ H
      · rcases htc s hsH hst.symm with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · have hk : t⁻¹ * s ∈ H := by
          have := (Subgroup.mul_mem_iff_of_index_two hind (a := ⟨t⁻¹, S.inv_mem htS⟩)
            (b := ⟨s, hs⟩)).2 (iff_of_false (fun h' => htH (by simpa using H.inv_mem h')) hsH)
          exact this
        have hkt : t * (t⁻¹ * s) = (t⁻¹ * s) * t := by
          calc t * (t⁻¹ * s) = s := by group
            _ = t⁻¹ * (t * s) := by group
            _ = t⁻¹ * (s * t) := by rw [hst]
            _ = (t⁻¹ * s) * t := by group
        rcases htc _ hk hkt with h | h
        · right; right; left
          calc s = t * (t⁻¹ * s) := by group
            _ = t := by rw [h, mul_one]
        · right; right; right
          calc s = t * (t⁻¹ * s) := by group
            _ = t * z := by rw [h]
    · rintro (rfl | rfl | rfl | rfl)
      · group
      · exact htz.symm
      · rfl
      · calc t * z * t = t * (z * t) := by group
          _ = t * (t * z) := by rw [htz]
  set t' : S := ⟨t, htS⟩
  set V : Subgroup S := centralizer ({t'} : Set S) with hV
  have hVmem : ∀ v : S, v ∈ V ↔ (v : P) = 1 ∨ (v : P) = z ∨ (v : P) = t ∨ (v : P) = t * z := by
    intro v
    rw [hV, mem_centralizer_singleton_iff, ← hmemV v v.2]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hcomm4 : ∀ a b : P, (a = 1 ∨ a = z ∨ a = t ∨ a = t * z) →
      (b = 1 ∨ b = z ∨ b = t ∨ b = t * z) → a * b = b * a := by
    have hzc : ∀ w : P, (w = 1 ∨ w = z ∨ w = t ∨ w = t * z) → w * z = z * w := by
      rintro w (rfl | rfl | rfl | rfl)
      · group
      · rfl
      · exact htz
      · calc t * z * z = z * t * z := by rw [htz]
          _ = z * (t * z) := by group
    have htc' : ∀ w : P, (w = 1 ∨ w = z ∨ w = t ∨ w = t * z) → w * t = t * w := by
      intro w hw
      exact (hmemV w (by
        rcases hw with rfl | rfl | rfl | rfl
        · exact one_mem S
        · exact hHS hzH
        · exact htS
        · exact S.mul_mem htS (hHS hzH))).2 hw
    intro a b ha hb
    rcases hb with rfl | rfl | rfl | rfl
    · group
    · exact hzc a ha
    · exact htc' a ha
    · rw [← mul_assoc, htc' a ha, mul_assoc, hzc a ha, ← mul_assoc]
  have hVab : IsMulCommutative V := by
    refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
    exact hcomm4 _ _ ((hVmem a).1 a.2) ((hVmem b).1 b.2)
  have hVexp : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    apply Subtype.ext
    change (v : P) ^ 2 = 1
    rcases (hVmem v).1 hv with h | h | h | h <;> rw [h]
    · exact one_pow 2
    · exact hz2
    · exact ht2
    · rw [pow_two, mul_assoc, ← mul_assoc z, ← htz, mul_assoc, ← mul_assoc t t, ← pow_two,
        ← pow_two, ht2, hz2, one_mul]
  have hVcard : Nat.card V = 4 := by
    have hmap : ((V.map S.subtype : Subgroup P) : Set P) = {1, z, t, t * z} := by
      ext x
      simp only [coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_insert_iff,
        Set.mem_singleton_iff, coe_subtype]
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact (hVmem v).1 hv
      · intro hx
        have hxS : x ∈ S := by
          rcases hx with rfl | rfl | rfl | rfl
          · exact one_mem S
          · exact hHS hzH
          · exact htS
          · exact S.mul_mem htS (hHS hzH)
        exact ⟨⟨x, hxS⟩, (hVmem ⟨x, hxS⟩).2 hx, rfl⟩
    rw [← Subgroup.card_map_of_injective S.subtype_injective]
    change Nat.card ((V.map S.subtype : Subgroup P) : Set P) = 4
    rw [hmap, Nat.card_coe_set_eq]
    have hzt : z ≠ t := fun h => htH (h ▸ hzH)
    have h1z : (1 : P) ≠ z := fun h => hz1 h.symm
    have h1t : (1 : P) ≠ t := fun h => ht1 h.symm
    have h1tz : (1 : P) ≠ t * z := by
      intro h
      apply hzt
      have : z = t⁻¹ := by
        calc z = t⁻¹ * (t * z) := by group
          _ = t⁻¹ := by rw [← h, mul_one]
      rw [this, htinv]
    have hztz : z ≠ t * z := by
      intro h
      apply ht1
      calc t = t * z * z⁻¹ := by group
        _ = 1 := by rw [← h, mul_inv_cancel]
    have httz : t ≠ t * z := by
      intro h
      apply hz1
      calc z = t⁻¹ * (t * z) := by group
        _ = 1 := by rw [← h, inv_mul_cancel]
    rw [Set.ncard_insert_of_notMem (by simp [h1z, h1t, h1tz]),
      Set.ncard_insert_of_notMem (by simp [hzt, hztz]), Set.ncard_pair httz]
  have hVcent : centralizer (V : Set S) = V := by
    apply le_antisymm
    · intro s hs
      rw [mem_centralizer_iff] at hs
      have ht'V : t' ∈ V := by
        rw [hVmem]
        right; right; left; rfl
      rw [hV, mem_centralizer_singleton_iff]
      exact (hs t' ht'V).symm
    · exact (le_centralizer_iff_isMulCommutative).2 hVab
  refine ⟨RankTwoShapes.selfCentralizing_four_shapes (hP.to_subgroup S) V hVab hVexp hVcard
    hVcent, ⟨V.map S.subtype, map_subtype_le V, ?_, ?_, ?_⟩, hcmp⟩
  · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨a', ha', hae⟩ := a.2
    obtain ⟨b', hb', hbe⟩ := b.2
    change (a : P) * b = b * a
    rw [← hae, ← hbe]
    exact congrArg (fun w : V => ((w : S) : P))
      (isMulCommutative_iff.mp hVab ⟨a', ha'⟩ ⟨b', hb'⟩)
  · rintro e ⟨v, hv, rfl⟩
    exact congrArg Subtype.val (hVexp v hv)
  · rw [Subgroup.card_map_of_injective S.subtype_injective, hVcard]

end TwoGroup

end CFSG.ComponentClassification.AschbacherKnownGroup
