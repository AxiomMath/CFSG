module

public import CFSG.GH74.Uniqueness.Section16Conf
public import CFSG.GH74.Uniqueness.Theorem4

public section

namespace CFSG.GH74.Uniqueness.Cor166

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem two_le_pRank_of_commuting {A : Subgroup X} {y z : X} (hy2 : orderOf y = 2)
    (hz2 : orderOf z = 2) (hyA : y ∈ A) (hzA : z ∈ A) (hne : y ≠ z) (hyz : y * z = z * y) :
    2 ≤ Open.pRank 2 A := by
  have h2 : 2 ≤ Open.twoRank ↥A :=
    CFSG.TwoRankLowerBound.Helpers.two_le_twoRank_of_commuting_involutions _ ⟨z, hzA⟩ ⟨y, hyA⟩
      (by rw [Subgroup.orderOf_mk]; exact hz2) (by rw [Subgroup.orderOf_mk]; exact hy2)
      (fun hh => hne (congrArg Subtype.val hh).symm) (Subtype.ext hyz.symm)
  have h3 := CFSG.SectionRank.pRank_le_map Nat.one_lt_two A.subtype
    Subtype.val_injective (⊤ : Subgroup ↥A)
  have h4 : (⊤ : Subgroup ↥A).map A.subtype = A := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h4] at h3
  exact h2.trans h3

theorem not_mem_Z_of_mem_inf (S : ZDSetup X Z M) {t y : X} (htM : t ∉ M)
    (hy : y ∈ M ⊓ conjugate M t) : y ∉ Z := by
  intro hyZ
  obtain ⟨β, -, huniq⟩ := S.prodDisc.existsUnique_fixed_point S.invariant hyZ
  have h1 := huniq M ⟨self_mem_omega M,
    (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr (Subgroup.mem_inf.mp hy).1⟩
  have hβ : conjugate M t ∈ omega M := ⟨t, rfl⟩
  have h2 := huniq (conjugate M t) ⟨hβ,
    (S.prodDisc.conjugate_eq_iff_mem hβ).mpr (Subgroup.mem_inf.mp hy).2⟩
  have h3 : conjugate M t = M := h2.trans h1.symm
  apply htM
  have := conjugate_eq_iff_mem_normalizer.mp h3
  rwa [S.prodDisc.normalizer_eq_self] at this

theorem conjugate_ne_self (S : ZDSetup X Z M) {t : X} (htM : t ∉ M) : M ≠ conjugate M t :=
  fun h => htM ((S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mp h.symm)

section Conf

variable (c : Conf16 Z M)

theorem u_mem_M : c.u ∈ M := (Subgroup.mem_inf.mp c.hu).1

theorem u_mem_Mt : c.u ∈ conjugate M c.t := (Subgroup.mem_inf.mp c.hu).2

theorem u_mul_self : c.u * c.u = 1 := by
  have := pow_orderOf_eq_one c.u
  rwa [c.hu2, sq] at this

theorem u_ne_one : c.u ≠ 1 := by
  intro h
  have h2 := c.hu2
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem u_inv : c.u⁻¹ = c.u := inv_eq_of_mul_eq_one_right (u_mul_self c)

theorem u_mem_B : c.u ∈ c.B := Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem comm_u_of_mem_B {x : X} (hx : x ∈ c.B) : x * c.u = c.u * x :=
  Subgroup.mem_centralizer_singleton_iff.mp hx

theorem B0_le_B : c.B0 ≤ c.B := Cor713.zHull_le _

theorem B_le_normalizer (S : ZDSetup X Z M) : c.B ≤ normalizer (c.B0 : Set X) :=
  le_normalizer_zHull S.invariant c.B

theorem mem_B0_of_mem_Z {y : X} (hy : y ∈ Z) (hyB : y ∈ c.B) : y ∈ c.B0 :=
  Subgroup.subset_closure ⟨hy, hyB⟩

theorem T1_le_B : c.T1 ≤ c.B := c.hT1.le.trans inf_le_left

theorem T1_le_M : c.T1 ≤ M := c.hT1.le.trans inf_le_right

theorem P_le_B0 : c.P ≤ c.B0 := c.hP.le.trans inf_le_left

theorem P_le_M : c.P ≤ M := c.hP.le.trans inf_le_right

theorem Q_le_P : c.Q ≤ c.P := (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem Q_le_B0 : c.Q ≤ c.B0 := (Q_le_P c).trans (P_le_B0 c)

theorem u_mem_T1 : c.u ∈ c.T1 := mem_of_isSylowOf_centralizer (u_mem_M c) c.hu2 c.hT1

theorem u_mem_J : c.u ∈ c.J := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact comm_u_of_mem_B c (B0_le_B c hx)

theorem z_mem_T1 : c.z ∈ c.T1 := c.hz_T1.1

theorem z_mem_B0 : c.z ∈ c.B0 := mem_B0_of_mem_Z c c.hz (T1_le_B c (z_mem_T1 c))

theorem t_mem_B0 : c.t ∈ c.B0 := mem_B0_of_mem_Z c c.ht c.ht_B

theorem inf_B0_eq_P : c.T1 ⊓ c.B0 = c.P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact c.hP.eq_of_le (le_inf c.hPT1 (P_le_B0 c))
    (le_inf inf_le_right (inf_le_left.trans (T1_le_M c))) (c.hT1.isPGroup.to_le inf_le_left)

theorem z_mem_P : c.z ∈ c.P := by
  rw [← inf_B0_eq_P c]
  exact ⟨z_mem_T1 c, z_mem_B0 c⟩

theorem u_not_mem_Z (S : ZDSetup X Z M) : c.u ∉ Z := not_mem_Z_of_mem_inf S c.htM c.hu

theorem u_ne_z (S : ZDSetup X Z M) : c.u ≠ c.z := fun h => u_not_mem_Z c S (h ▸ c.hz)

theorem z_comm_u : c.z * c.u = c.u * c.z := comm_u_of_mem_B c (T1_le_B c (z_mem_T1 c))

theorem u_not_mem_B0 (S : ZDSetup X Z M) {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e) :
    c.u ∉ c.B0 := fun h => u_not_mem_Z c S (hB.invol c.u h c.hu2)

end Conf

theorem false_of_four_fix_two
    (S : ZDSetup X Z M) (c : Conf16 Z M) (h165 : Prop165Stmt Z M)
    {a b : X} (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (hcomm : a * b = b * a)
    {γ δ : Subgroup X} (hγ : γ ∈ omega M) (hδ : δ ∈ omega M) (hγδ : γ ≠ δ)
    (haγ : a ∈ γ) (hbγ : b ∈ γ) (haδ : a ∈ δ) (hbδ : b ∈ δ) : False := by
  obtain ⟨g, hg1, hg2⟩ := S.theorem4.1 γ hγ δ hδ hγδ M (self_mem_omega M) (conjugate M c.t)
    ⟨c.t, rfl⟩ (conjugate_ne_self S c.htM)
  have hmem : ∀ x : X, x ∈ γ → x ∈ δ → g⁻¹ * x * g ∈ c.D := by
    intro x hxγ hxδ
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← hg1, mem_conjugate_iff]
      simpa [mul_assoc] using hxγ
    · rw [← hg2, mem_conjugate_iff]
      simpa [mul_assoc] using hxδ
  have hord : ∀ x : X, orderOf (g⁻¹ * x * g) = orderOf x := fun x => by
    have h : SemiconjBy g⁻¹ x (g⁻¹ * x * g) := by
      unfold SemiconjBy
      group
    exact (SemiconjBy.orderOf_eq _ h).symm
  have h2 := two_le_pRank_of_commuting (A := c.D) (by rw [hord]; exact ha) (by rw [hord]; exact hb)
    (hmem a haγ haδ) (hmem b hbγ hbδ)
    (fun h => hab (by simpa using congrArg (fun x => g * x * g⁻¹) h))
    (by
      calc g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
        _ = g⁻¹ * (b * a) * g := by rw [hcomm]
        _ = g⁻¹ * b * g * (g⁻¹ * a * g) := by group)
  have h1 := h165 c
  omega

theorem mem_M_of_comm
    (S : ZDSetup X Z M) (c : Conf16 Z M) (h165 : Prop165Stmt Z M) {v : X}
    (hv2 : orderOf v = 2) (hvu : v ≠ c.u) (hvM : v ∈ M) (hvB : v ∈ c.B) {x : X} (hx : x ∈ c.B0)
    (hxv : v * x = x * v) : x ∈ M := by
  by_contra hxM
  have hγ : conjugate M x ∈ omega M := ⟨x, rfl⟩
  have hne : conjugate M x ≠ M := fun h =>
    hxM ((S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mp h)
  have hxu : x * c.u * x⁻¹ = c.u := by
    rw [comm_u_of_mem_B c (B0_le_B c hx)]
    group
  have hxv' : x * v * x⁻¹ = v := by
    rw [← hxv]
    group
  refine false_of_four_fix_two S c h165 c.hu2 hv2 hvu.symm (comm_u_of_mem_B c hvB).symm hγ
    (self_mem_omega M) hne ?_ ?_ (u_mem_M c) hvM
  · rw [mem_conjugate_iff, hxu]
    exact u_mem_M c
  · rw [mem_conjugate_iff, hxv']
    exact hvM

omit [Finite X] in
theorem mem_or_mul_mem_of_mem_sup {Q : Subgroup X} {u : X} (hu2 : u * u = 1)
    (hcomm : ∀ q ∈ Q, q * u = u * q) {x : X} (hx : x ∈ Q ⊔ zpowers u) : x ∈ Q ∨ x * u ∈ Q := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hc : ∀ y : X, y * u ∈ Q → y * u = u * y := by
    intro y hy
    have h1 := hcomm _ hy
    calc y * u = y * u * u * u⁻¹ := by group
      _ = u * (y * u) * u⁻¹ := by rw [h1]
      _ = u * y * (u * u⁻¹) := by group
      _ = u * y := by rw [mul_inv_cancel, mul_one]
  let H : Subgroup X :=
    { carrier := {y | y ∈ Q ∨ y * u ∈ Q}
      one_mem' := Or.inl Q.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (Q.mul_mem ha hb)
        · exact Or.inr (by rw [mul_assoc]; exact Q.mul_mem ha hb)
        · refine Or.inr ?_
          have : a * b * u = a * u * b := by
            rw [mul_assoc, hcomm b hb, ← mul_assoc]
          rw [this]
          exact Q.mul_mem ha hb
        · refine Or.inl ?_
          have : a * b = a * u * (b * u) := by
            calc a * b = a * (u * u) * b := by rw [hu2, mul_one]
              _ = a * u * (u * b) := by group
              _ = a * u * (b * u) := by rw [hc b hb]
          rw [this]
          exact Q.mul_mem ha hb
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (Q.inv_mem ha)
        · refine Or.inr ?_
          have : a⁻¹ * u = (a * u)⁻¹ := by
            rw [mul_inv_rev, hui]
            have h1 := hc a ha
            calc a⁻¹ * u = a⁻¹ * (a * u) * a⁻¹ := by
                  rw [h1]; group
              _ = u * a⁻¹ := by group
          rw [this]
          exact Q.inv_mem ha }
  have hle : Q ⊔ zpowers u ≤ H := by
    refine sup_le (fun q hq => Or.inl hq) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr (by rw [hu2]; exact Q.one_mem)
  exact hle hx

end CFSG.GH74.Uniqueness.Cor166
