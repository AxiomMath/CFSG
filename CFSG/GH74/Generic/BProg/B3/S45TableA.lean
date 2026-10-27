module

public import CFSG.GH74.Generic.BProg.B3.FalseCtxS45Glue
public import CFSG.GH74.Generic.BProg.B3.L2CompAlt7
public import CFSG.GH74.Generic.BProg.B3.L2CompL2
public import CFSG.GH74.Generic.BProg.B3.L2CompL3
public import CFSG.GH74.Generic.BProg.B3.L2CompU3Data
public import CFSG.GH74.Generic.BProg.B3.L2CompBasic

public section

namespace CFSG.GH74.Generic.BProg.B3.S45TableA

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint Subgroup

@[expose] def Datum (X : Type) [Group X] (y : MulAut X) : Prop :=
  ∃ (V Q : Type) (_ : Group V) (_ : Group Q) (π : V →* X) (ψ : V →* Q),
    (∀ v, y (π v) = π v) ∧ π.ker ≤ ψ.ker ∧ Function.Surjective ψ ∧ Odd (Nat.card ψ.ker) ∧
      HasL2Model Q Odd

structure Hyp5w (X : Type) [Group X] (y : MulAut X) : Prop where
  ord : orderOf y = 2
  abelian : ∀ T : Subgroup X, IsPGroup 2 ↥T → (∀ t ∈ T, y t = t) → ∀ a ∈ T, ∀ b ∈ T, a * b = b * a
  datum : Datum X y

theorem Hyp5w.false_of_dihedral {X : Type} [Group X] {y : MulAut X} (h : Hyp5w X y) {a b : X}
    (ha : y a = a) (hb : y b = b) (ha4 : a ^ 4 = 1) (ha2 : a ^ 2 ≠ 1) (hb2 : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) : False := by
  have hT := L2CompBasic.isPGroup_closure_dihedral ha4 hb2 hba
  have hle : closure ({a, b} : Set X) ≤ B2.fixedIn X (zpowers y) := by
    rw [Subgroup.closure_le]
    rintro t (rfl | rfl)
    · exact L2CompBasic.mem_fixedIn_zpowers_iff.2 ha
    · exact L2CompBasic.mem_fixedIn_zpowers_iff.2 hb
  have hcomm := h.abelian _ hT (fun t ht => L2CompBasic.mem_fixedIn_zpowers_iff.1 (hle ht)) a
    (Subgroup.subset_closure (by simp)) b (Subgroup.subset_closure (by simp))
  have h1 : b * a = a * b := hcomm.symm
  have h2 : a⁻¹ = a := by
    calc a⁻¹ = b * a * b⁻¹ := hba.symm
      _ = a * b * b⁻¹ := by rw [h1]
      _ = a := by simp
  apply ha2
  rw [pow_two]
  exact mul_eq_one_iff_eq_inv.2 h2.symm

section DatumFacts

variable {X V Q : Type} [Group X] [Group V] [Group Q]

theorem finite_Q (hQ : HasL2Model Q Odd) : Finite Q := by
  obtain ⟨-, -, -, q, hq5, -, hcard, -⟩ := S45.LAlt.hasL2Model_data hQ
  have h25 : 25 ≤ q ^ 2 := by nlinarith
  have hpos : 0 < q * (q ^ 2 - 1) := Nat.mul_pos (by omega) (by omega)
  have : Nat.card Q ≠ 0 := by
    intro h0
    rw [h0] at hcard
    omega
  exact Nat.finite_of_card_ne_zero this

theorem finite_V (ψ : V →* Q) (hψ : Function.Surjective ψ) (hodd : Odd (Nat.card ψ.ker))
    (hQ : HasL2Model Q Odd) : Finite V := by
  have := finite_Q hQ
  have h1 : Nat.card ψ.ker ≠ 0 := hodd.pos.ne'
  have h2 : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have h3 := Subgroup.card_ker_mul_card_of_surjective hψ
  exact Nat.finite_of_card_ne_zero (by rw [← h3]; exact Nat.mul_ne_zero h1 h2)

theorem eq_one_of_two_pow_of_mem_odd {G : Type} [Group G] {H : Subgroup G} (hH : Odd (Nat.card H)) {g : G}
    (hg : g ∈ H) {k : ℕ} (hk : g ^ (2 ^ k) = 1) : g = 1 := by
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h2 : orderOf g ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H hg
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0, pow_zero] at hj
    exact orderOf_eq_one_iff.1 hj
  · exfalso
    have h3 : 2 ∣ orderOf g := by rw [hj]; exact dvd_pow_self 2 hpos.ne'
    exact (Nat.not_even_iff_odd.2 hH) (even_iff_two_dvd.2 (h3.trans h2))

theorem psi_eq_one_of_mem_center {π : V →* X} {ψ : V →* Q} (hker : π.ker ≤ ψ.ker)
    (hψ : Function.Surjective ψ) (hQs : IsSimpleGroup Q) (hQn : ∃ a b : Q, a * b ≠ b * a) {v : V}
    (hv : π v ∈ Subgroup.center X) : ψ v = 1 := by
  set U : Subgroup V := (Subgroup.center X).comap π with hU
  have hUn : U.Normal := (inferInstance : (Subgroup.center X).Normal).comap π
  have hmn : (U.map ψ).Normal := hUn.map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (U.map ψ) with h | h
  · have h1 : ψ v ∈ U.map ψ := ⟨v, hv, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := hQn
    have ha : a ∈ U.map ψ := h ▸ Subgroup.mem_top a
    have hb : b ∈ U.map ψ := h ▸ Subgroup.mem_top b
    obtain ⟨u₁, hu₁, rfl⟩ := ha
    obtain ⟨u₂, hu₂, rfl⟩ := hb
    have hc : u₁ * u₂ * u₁⁻¹ * u₂⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      have h1 : π u₂ * π u₁ = π u₁ * π u₂ := Subgroup.mem_center_iff.1 hu₁ (π u₂)
      rw [← h1]
      group
    have h2 := hker hc
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    apply hab
    have h3 : ψ u₁ * ψ u₂ * (ψ u₁)⁻¹ * (ψ u₂)⁻¹ = 1 := h2
    calc ψ u₁ * ψ u₂ = (ψ u₁ * ψ u₂ * (ψ u₁)⁻¹ * (ψ u₂)⁻¹) * (ψ u₂ * ψ u₁) := by group
      _ = ψ u₂ * ψ u₁ := by rw [h3, one_mul]

theorem exists_invol_lift [Finite V] (ψ : V →* Q) (hψ : Function.Surjective ψ)
    (hodd : Odd (Nat.card ψ.ker)) (hQ : HasL2Model Q Odd) : ∃ w : V, orderOf w = 2 ∧ ψ w ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, ⟨q, hq⟩, -⟩ := S45.LAlt.hasL2Model_data hQ
  have : Finite Q := finite_Q hQ
  have h2Q : 2 ∣ Nat.card Q := hq ▸ orderOf_dvd_natCard q
  have h2V : 2 ∣ Nat.card V := h2Q.trans (Subgroup.card_dvd_of_surjective hψ)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 h2V
  refine ⟨w, hw, fun h1 => ?_⟩
  have hwk : w ∈ ψ.ker := h1
  have h3 : orderOf w ∣ Nat.card ψ.ker := Subgroup.orderOf_dvd_natCard ψ.ker hwk
  rw [hw] at h3
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h3)

theorem card_dvd_range [Finite X] {π : V →* X} {ψ : V →* Q} (hker : π.ker ≤ ψ.ker)
    (hψ : Function.Surjective ψ) : Nat.card Q ∣ Nat.card π.range := by
  have hk : π.rangeRestrict.ker ≤ ψ.ker := by rwa [MonoidHom.ker_rangeRestrict]
  set φ : ↥π.range →* Q :=
    (MonoidHom.liftOfSurjective π.rangeRestrict π.rangeRestrict_surjective) ⟨ψ, hk⟩ with hφdef
  have hφ : ∀ v, φ (π.rangeRestrict v) = ψ v := fun v => by simp [φ]
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨v, rfl⟩ := hψ q
    exact ⟨π.rangeRestrict v, hφ v⟩
  exact Subgroup.card_dvd_of_surjective hφs

end DatumFacts

section DihedralLeaves

open Equiv Equiv.Perm

theorem false_of_alt7 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7)) {y : MulAut X}
    (h5 : Hyp5w X y) : False := by
  have hy2 : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [h5.ord, pow_two] at h
    exact h
  have hy1 : y ≠ 1 := by
    intro h
    have := h5.ord
    rw [h, orderOf_one] at this
    omega
  set α : MulAut (alternatingGroup (Fin 7)) := MulAut.congr e y with hα
  have hα2 : α * α = 1 := by rw [hα, ← map_mul, hy2, map_one]
  obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation (Or.inr (by norm_num)) α
  have hσ2 : σ * σ = 1 := by
    apply L2CompAlt7.eq_one_of_comm_alt
    intro g
    have h1 : (α (α g) : L2CompAlt7.P7) = σ * (σ * (g : L2CompAlt7.P7) * σ⁻¹) * σ⁻¹ := by
      rw [hσ, hσ]
    have h2 : α (α g) = g := by
      have := congrArg (fun φ : MulAut (alternatingGroup (Fin 7)) => φ g) hα2
      simpa using this
    rw [h2] at h1
    have h3 : σ * σ * (g : L2CompAlt7.P7) * (σ * σ)⁻¹ = (g : L2CompAlt7.P7) := by
      calc σ * σ * (g : L2CompAlt7.P7) * (σ * σ)⁻¹
          = σ * (σ * (g : L2CompAlt7.P7) * σ⁻¹) * σ⁻¹ := by group
        _ = (g : L2CompAlt7.P7) := h1.symm
    calc σ * σ * (g : L2CompAlt7.P7)
        = σ * σ * (g : L2CompAlt7.P7) * (σ * σ)⁻¹ * (σ * σ) := by group
      _ = ((g : L2CompAlt7.P7)) * (σ * σ) := by rw [h3]
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hy1
    have hα1 : α = 1 := by
      ext g
      rw [hσ, h]
      simp
    have : MulAut.congr e y = 1 := hα1
    exact (MulAut.congr e).injective (by rw [this, map_one])
  obtain ⟨a, b, hsa, hsb, hσa, hσb, ha4, ha2, hb2, hba⟩ := L2CompAlt7.exists_D8_of_invol σ hσ2 hσ1
  let A : alternatingGroup (Fin 7) := ⟨a, mem_alternatingGroup.2 hsa⟩
  let B : alternatingGroup (Fin 7) := ⟨b, mem_alternatingGroup.2 hsb⟩
  have hαA : α A = A := by
    apply Subtype.ext
    rw [hσ]
    show σ * a * σ⁻¹ = a
    rw [hσa]
    group
  have hαB : α B = B := by
    apply Subtype.ext
    rw [hσ]
    show σ * b * σ⁻¹ = b
    rw [hσb]
    group
  have hyfix : ∀ g : alternatingGroup (Fin 7), α g = g → y (e.symm g) = e.symm g := by
    intro g hg
    have : e.symm (α g) = y (e.symm g) := by
      rw [hα, MulAut.congr_apply]
      simp
    rw [← this, hg]
  refine h5.false_of_dihedral (a := e.symm A) (b := e.symm B) (hyfix A hαA) (hyfix B hαB) ?_ ?_ ?_ ?_
  · rw [← map_pow]
    have : A ^ 4 = 1 := Subtype.ext (by simpa [A] using ha4)
    rw [this, map_one]
  · intro h
    rw [← map_pow] at h
    have h' : A ^ 2 = 1 := e.symm.injective (by rw [h, map_one])
    exact ha2 (by simpa [A] using congrArg Subtype.val h')
  · rw [← map_mul]
    have : B * B = 1 := Subtype.ext (by simpa [B] using hb2)
    rw [this, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    apply Subtype.ext
    simpa [A, B] using hba

end DihedralLeaves

section L3U3

variable {X : Type} [Group X] [Finite X] {y : MulAut X}

theorem false_of_l3 (hXs : IsSimpleGroup X) (hnab : ∃ a b : X, a * b ≠ b * a) {p f : ℕ}
    (hp2 : p ≠ 2) (hm : LieModel X .PSL 3 p f) (h5 : Hyp5w X y) : False := by
  have hstated := CFSG.GH74.Generic.stated_of_lieModel_PSL hm
  have hy2 : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [h5.ord, pow_two] at h
    exact h
  have hy1 : y ≠ 1 := by
    intro h
    have h2 := h5.ord
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨a, b, ha, hb, ha4, ha2, hb2, hba⟩ :=
    L2CompL3.psl_three_fixed_D8 hXs hnab hp2 hstated hy2 hy1
  exact h5.false_of_dihedral ha hb ha4 ha2 hb2 hba

theorem false_of_u3 {p f : ℕ} (hp2 : p ≠ 2) (hm : LieModel X .PSU 3 p f) (h5 : Hyp5w X y) : False := by
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [h5.ord, pow_two] at this
  obtain ⟨a, b, ha, hb, ha4, ha2, hb2, hba⟩ :=
    L2CompU3Data.psu_fixed_data_D8 hp2 (stated_of_lieModel_PSU hm) hy2
  exact h5.false_of_dihedral ha hb ha4 ha2 hb2 hba

end L3U3

section L2

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.AutL2Facts CFSG.GH74.Generic.S45 CFSG.LinearGroups
open CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
open CFSG.GH74.Generic.BProg.B3.L2CompL2Field
open scoped MatrixGroups

theorem psl2_linear_false_w
    {F : Type} [Field F] [Finite F] (hK : IsOddPrimePower (Nat.card F))
    {S V Q : Type} [Group S] [Finite S] [Group V] [Group Q] (e : S ≃* PSL2 F) {y : MulAut S}
    (π : V →* S) (ψ : V →* Q) (hfix : ∀ v, y (π v) = π v) (hker : π.ker ≤ ψ.ker)
    (hψ : Function.Surjective ψ) (hodd : Odd (Nat.card ψ.ker)) (hQ : HasL2Model Q Odd)
    (hne : y ≠ 1) {C : PGL2 F} (hC : autEquiv e y = SemidirectProduct.inl C) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQs, hQn, -, -⟩ := S45.LAlt.hasL2Model_data hQ
  have hQf : Finite Q := finite_Q hQ
  have hVf : Finite V := finite_V ψ hψ hodd hQ
  let Φ : S →* PGL2 F :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp e.toMonoidHom
  have hΦ : Function.Injective Φ :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp e.injective
  have hcomm : ∀ s : S, y s = s → Φ s * C = C * Φ s := by
    intro s hs
    have h1 := semilinearAction_autEquiv_apply e y s
    rw [hC, semilinearAction_inl] at h1
    rw [hs] at h1
    have h3 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h1
    rw [toPGL_pglAction] at h3
    change Matrix.ProjectiveSpecialLinearGroup.toPGL (e s) * C =
      C * Matrix.ProjectiveSpecialLinearGroup.toPGL (e s)
    calc Matrix.ProjectiveSpecialLinearGroup.toPGL (e s) * C
        = (C * Matrix.ProjectiveSpecialLinearGroup.toPGL (e s) * C⁻¹) * C := by rw [h3]
      _ = C * Matrix.ProjectiveSpecialLinearGroup.toPGL (e s) := by group
  obtain ⟨W, hW⟩ := L2CompL2.exists_kleinFour_of_hasL2Model hQ
  have hW2 : IsPGroup 2 ↥W := IsPGroup.of_card (n := 2) (by rw [hW.card_four]; rfl)
  obtain ⟨P, hPp, hPmap⟩ := FalseCtxS45.exists_pGroup_lift ψ W hW2
    (by rw [MonoidHom.range_eq_top_of_surjective ψ hψ]; exact le_top)
  have hkerodd : Odd (Nat.card ψ.ker) := hodd
  have hPinj : ∀ p ∈ P, ψ p = 1 → p = 1 := by
    intro p hp hψp
    obtain ⟨k, hk⟩ := hPp ⟨p, hp⟩
    exact eq_one_of_two_pow_of_mem_odd hkerodd (MonoidHom.mem_ker.2 hψp)
      (k := k) (congrArg Subtype.val hk)
  have hπinj : ∀ p ∈ P, π p = 1 → p = 1 := fun p hp h1 =>
    hPinj p hp (MonoidHom.mem_ker.1 (hker (MonoidHom.mem_ker.2 h1)))
  let g : ↥P →* PGL2 F := (Φ.comp π).comp P.subtype
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have h1 : Φ (π (p : V)) = 1 := hp
    have h2 : π (p : V) = 1 := hΦ (by rw [h1, map_one])
    exact Subtype.ext (hπinj p p.2 h2)
  let eP : ↥P ≃* ↥W := MulEquiv.ofBijective
    ((ψ.comp P.subtype).codRestrict W (fun p => hPmap ▸ ⟨p, p.2, rfl⟩))
    ⟨by
      rw [injective_iff_map_eq_one]
      intro p hp
      have h1 : ψ (p : V) = 1 := congrArg Subtype.val hp
      exact Subtype.ext (hPinj p p.2 h1),
     by
      rintro ⟨w, hw⟩
      have hw' : w ∈ P.map ψ := hPmap ▸ hw
      obtain ⟨p, hp, rfl⟩ := hw'
      exact ⟨⟨p, hp⟩, rfl⟩⟩
  let eg : ↥P ≃* ↥g.range := MonoidHom.ofInjective hg
  have hK4 : IsKleinFour ↥g.range :=
    { card_four := (Nat.card_congr eg.toEquiv).symm.trans
        ((Nat.card_congr eP.toEquiv).trans hW.card_four)
      exponent_two := (Monoid.exponent_eq_of_mulEquiv eg.symm).trans
        ((Monoid.exponent_eq_of_mulEquiv eP).trans hW.exponent_two) }
  have hcent := pgl2_kleinFour_centralizer_eq_self F hK g.range hK4
  have hCmem : C ∈ g.range := by
    rw [← hcent, Subgroup.mem_centralizer_iff]
    rintro _ ⟨p, rfl⟩
    exact hcomm (π p) (hfix p)
  obtain ⟨p₀, hp₀⟩ := hCmem
  have hp₀' : Φ (π (p₀ : V)) = C := hp₀
  have hzc : ψ (p₀ : V) ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨v, rfl⟩ := hψ q
    have h1 : Φ (π v) * Φ (π (p₀ : V)) = Φ (π (p₀ : V)) * Φ (π v) := by
      rw [hp₀']
      exact hcomm (π v) (hfix v)
    have h2 : π v * π (p₀ : V) = π (p₀ : V) * π v := hΦ (by rw [map_mul, map_mul]; exact h1)
    have h3 : v * (p₀ : V) * v⁻¹ * (p₀ : V)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h2]
      group
    have h4 := hker h3
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at h4
    have h5 : ψ v * ψ (p₀ : V) * (ψ v)⁻¹ * (ψ (p₀ : V))⁻¹ = 1 := h4
    calc ψ v * ψ (p₀ : V) = (ψ v * ψ (p₀ : V) * (ψ v)⁻¹ * (ψ (p₀ : V))⁻¹) * (ψ (p₀ : V) * ψ v) := by
          group
      _ = ψ (p₀ : V) * ψ v := by rw [h5, one_mul]
  have hZ : Subgroup.center Q = ⊥ := center_eq_bot_of_simple_nonab hQs hQn
  rw [hZ, Subgroup.mem_bot] at hzc
  have hp₀1 : (p₀ : V) = 1 := hPinj p₀ p₀.2 hzc
  have hC1 : C = 1 := by rw [← hp₀', hp₀1, map_one, map_one]
  apply hne
  apply (autEquiv e).injective
  rw [hC, hC1, map_one, map_one]

theorem false_of_l2 {X : Type} [Group X] [Finite X]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hm : LieModel X .PSL 2 p f) {y : MulAut X}
    (h5 : Hyp5w X y) : False := by
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hm
  have hodd : IsOddPrimePower (Nat.card F) := isOddPrimePower_of hp hp2 hf hF
  have hk : ringChar F ≠ 2 := ringChar_ne_two_of_card_eq_pow hp hp2 hF
  let e : X ≃* PSL2 F := e₀.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hy1 : y ≠ 1 := by
    intro h
    have := h5.ord
    rw [h, orderOf_one] at this
    omega
  have hg : orderOf (autEquiv e y) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact h5.ord
  by_cases hfield : (autEquiv e y).right = 1
  · have hgl : autEquiv e y = SemidirectProduct.inl (autEquiv e y).left := by
      have h := SemidirectProduct.inl_left_mul_inr_right (autEquiv e y)
      rw [hfield, map_one, mul_one] at h
      exact h.symm
    obtain ⟨V, Q, _, _, π, ψ, hfix, hker, hψ, hodd', hQ⟩ := h5.datum
    exact psl2_linear_false_w hodd e π ψ hfix hker hψ hodd' hQ hy1 hgl
  · obtain ⟨x, z, hx, hz, hx4, hz2, hzx⟩ :=
      exists_fixed_D8_of_field hodd hk (autEquiv e y) hg hfield
    have hfix : ∀ t : PSL2 F, semilinearAction F (autEquiv e y) t = t → y (e.symm t) = e.symm t := by
      intro t ht
      have h := semilinearAction_autEquiv_apply e y (e.symm t)
      rw [MulEquiv.apply_symm_apply, ht] at h
      apply e.injective
      rw [← h, MulEquiv.apply_symm_apply]
    have hx4' : x ^ 4 = 1 := hx4 ▸ pow_orderOf_eq_one x
    have hx2 : x ^ 2 ≠ 1 := by
      intro h2
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hx4] at this
      omega
    refine h5.false_of_dihedral (a := e.symm x) (b := e.symm z) (hfix x hx) (hfix z hz) ?_ ?_ ?_ ?_
    · rw [← map_pow, hx4', map_one]
    · intro h
      rw [← map_pow] at h
      exact hx2 (e.symm.injective (by rw [h, map_one]))
    · rw [← map_mul, hz2, map_one]
    · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
      congr 1

end L2

end CFSG.GH74.Generic.BProg.B3.S45TableA
