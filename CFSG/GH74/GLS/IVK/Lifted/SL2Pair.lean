module

public import CFSG.GH74.GLS.IVK.Lifted.DihedralOuter
public import CFSG.GH74.GLS.IVK.Lifted.ExtendZ2
public import CFSG.GH74.GLS.IVK.Lifted.Lem31c

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4

theorem outer_sylow_conj_aux {G : Type} [Group G] [Finite G] (D N : Subgroup G)
    (hN2 : N.relIndex D = 2) {α : G} (hαD : α ∈ D) (hαN : α ∉ N) (hα2 : α * α = 1)
    {T₁ T₂ : Subgroup G} (h₁ : M.Syl2In T₁ D) (h₂ : M.Syl2In T₂ D) (hα₁ : α ∈ T₁) (hα₂ : α ∈ T₂)
    {m : ℕ} (hm : 1 ≤ m) (e₂ : ↥T₂ ≃* DihedralGroup (2 ^ m)) (hnc : ¬ IsCyclic ↥(N.subgroupOf T₂)) :
    ∃ h ∈ N, h * α * h⁻¹ = α ∧ ∀ x, x ∈ T₂ ↔ h * x * h⁻¹ ∈ T₁ := by
  have hidxD : (N.subgroupOf D).index = 2 := hN2
  have hmulD : ∀ a ∈ D, ∀ b ∈ D, a * b ∈ N ↔ (a ∈ N ↔ b ∈ N) := fun a ha b hb =>
    Subgroup.mul_mem_iff_of_index_two hidxD (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα2
  have hN0 : (N.subgroupOf T₂).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨α, hα₂⟩, fun b => ?_⟩
    have hbD : (b : G) ∈ D := h₂.1 b.2
    have h1 := hmulD (b : G) hbD α hαD
    have h2 : (b * ⟨α, hα₂⟩ ∈ N.subgroupOf T₂) ↔ ((b : G) * α ∈ N) := Iff.rfl
    have h3 : (b ∈ N.subgroupOf T₂) ↔ ((b : G) ∈ N) := Iff.rfl
    rw [h2, h3, h1]
    by_cases hb : (b : G) ∈ N <;> simp [hb, hαN]
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm1 : m = 1 := by omega
    subst hm1
    have hcardT : Nat.card ↥T₂ = 4 := by
      rw [Nat.card_congr e₂.toEquiv, DihedralGroup.nat_card]
      norm_num
    have hcardN : Nat.card ↥(N.subgroupOf T₂) = 2 := by
      have h := Subgroup.card_mul_index (N.subgroupOf T₂)
      rw [hN0, hcardT] at h
      omega
    exact hnc (isCyclic_of_prime_card hcardN)
  obtain ⟨c, hcD, hc⟩ := M.Syl2In.exists_conj h₁ h₂
  have hcT : ∀ x, x ∈ T₂ ↔ c * x * c⁻¹ ∈ T₁ := fun x => by rw [hc]; exact M.mem_cj
  have hαT₁ : ∀ y, y ∈ T₁ ↔ α⁻¹ * y * α ∈ T₁ := fun y => by
    constructor
    · intro hy
      exact T₁.mul_mem (T₁.mul_mem (T₁.inv_mem hα₁) hy) hα₁
    · intro hy
      have := T₁.mul_mem (T₁.mul_mem hα₁ hy) (T₁.inv_mem hα₁)
      simpa [mul_assoc] using this
  obtain ⟨n, hnN, hnT⟩ : ∃ n ∈ N, ∀ x, x ∈ T₂ ↔ n * x * n⁻¹ ∈ T₁ := by
    by_cases hcN : c ∈ N
    · exact ⟨c, hcN, hcT⟩
    · refine ⟨α⁻¹ * c, ?_, fun x => ?_⟩
      · exact (hmulD α⁻¹ (inv_mem hαD) c hcD).2 (iff_of_false (by rwa [hαi]) hcN)
      · rw [hcT x, hαT₁ (c * x * c⁻¹)]
        have : α⁻¹ * c * x * (α⁻¹ * c)⁻¹ = α⁻¹ * (c * x * c⁻¹) * α := by group
        rw [this]
  have hβT : n⁻¹ * α * n ∈ T₂ := by
    rw [hnT]
    have : n * (n⁻¹ * α * n) * n⁻¹ = α := by group
    rw [this]
    exact hα₁
  have hβN : n⁻¹ * α * n ∉ N := fun h => hαN (by
    have := N.mul_mem (N.mul_mem hnN h) (N.inv_mem hnN)
    simpa [mul_assoc] using this)
  have hβ2 : (n⁻¹ * α * n) * (n⁻¹ * α * n) = 1 := by
    calc (n⁻¹ * α * n) * (n⁻¹ * α * n) = n⁻¹ * (α * α) * n := by group
      _ = 1 := by rw [hα2]; group
  obtain ⟨p, hpN, hp⟩ := dihedral_outer_conj hm2 e₂ (N.subgroupOf T₂) hN0 hnc
    (x := ⟨n⁻¹ * α * n, hβT⟩) (y := ⟨α, hα₂⟩)
    (Subtype.ext (by simpa using hβ2)) (Subtype.ext (by simpa using hα2))
    (fun h => hβN h) (fun h => hαN h)
  have hpT : (p : G) ∈ T₂ := p.2
  have hpN' : (p : G) ∈ N := hpN
  have hpα : (p : G) * α * (p : G)⁻¹ = n⁻¹ * α * n := by
    have := congrArg Subtype.val hp
    simpa using this
  refine ⟨n * (p : G), N.mul_mem hnN hpN', ?_, fun x => ?_⟩
  · calc n * (p : G) * α * (n * (p : G))⁻¹ = n * ((p : G) * α * (p : G)⁻¹) * n⁻¹ := by group
      _ = α := by rw [hpα]; group
  · have hpx : x ∈ T₂ ↔ (p : G) * x * (p : G)⁻¹ ∈ T₂ := by
      constructor
      · intro hx
        exact T₂.mul_mem (T₂.mul_mem hpT hx) (T₂.inv_mem hpT)
      · intro hx
        have := T₂.mul_mem (T₂.mul_mem (T₂.inv_mem hpT) hx) hpT
        simpa [mul_assoc] using this
    rw [hpx, hnT]
    have : n * ((p : G) * x * (p : G)⁻¹) * n⁻¹ = n * (p : G) * x * (n * (p : G))⁻¹ := by group
    rw [this]

theorem mulAut_conj_conj {Q : Type} [Group Q] (α : MulAut Q) (y : Q) :
    α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := by
  ext z
  simp [MulAut.conj_apply]

theorem isPGroup_sup_zpowers_of_involution {G : Type} [Group G] [Finite G] {A : Subgroup G} {x : G}
    (hA : IsPGroup 2 ↥A) (hx2 : x * x = 1) (hxA : ∀ a ∈ A, x * a * x⁻¹ ∈ A) :
    IsPGroup 2 ↥(A ⊔ zpowers x) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxx : x ∈ A ⊔ zpowers x := mem_sup_right (mem_zpowers x)
  have hrel : A.relIndex (A ⊔ zpowers x) ≤ 2 :=
    relIndex_le_two_of_cover hxx (fun b hb => by
      rcases mem_sup_zpowers_cases hx2 hxA hb with h | ⟨n, hn, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨n, hn, rfl⟩) (fun p hp => by
      have h := hxA p hp
      rw [hxi] at h ⊢
      exact h)
  have hcard := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ zpowers x)
  rw [inf_eq_left.mpr le_sup_left] at hcard
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hpos : 0 < A.relIndex (A ⊔ zpowers x) := by
    rcases Nat.eq_zero_or_pos (A.relIndex (A ⊔ zpowers x)) with h | h
    · rw [h, zero_mul] at hcard
      exact absurd hcard.symm Nat.card_pos.ne'
    · exact h
  have : A.relIndex (A ⊔ zpowers x) = 1 ∨ A.relIndex (A ⊔ zpowers x) = 2 := by omega
  rcases this with h | h
  · rw [h, one_mul] at hcard
    exact IsPGroup.of_card (n := k) (by rw [← hcard, hk])
  · rw [h] at hcard
    exact IsPGroup.of_card (n := k + 1) (by rw [← hcard, hk, pow_succ]; ring)

section DihData

variable {F : Type} [Field F] [Finite F]

theorem dihedral_data_PSL (hL2 : L2Field F) {S : Subgroup (MulAut (PSL2 F))}
    (hS : M.Syl2In S (innDiagSub (L2.equivPSL F).symm))
    (hSN : M.Syl2In (S ⊓ innAut (PSL2 F)) (innAut (PSL2 F))) :
    (∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥S ≃* DihedralGroup (2 ^ m))) ∧
      ¬ IsCyclic ↥((innAut (PSL2 F)).subgroupOf S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_of_L2Field hL2
  have : Finite (PGL2 F) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 2) F →* PGL2 F)
      Matrix.ProjGenLinGroup.mk_surjective
  have hdihD : HasDihedralSylowTwo ↥(innDiagSub (L2.equivPSL F).symm) :=
    hasDihedralSylowTwo_of_equiv (innDiagEquiv (L2.equivPSL F).symm).symm
      (pgl2_odd_hasDihedralSylowTwo_model F hodd)
  have hdihN : HasDihedralSylowTwo ↥(innAut (PSL2 F)) :=
    hasDihedralSylowTwo_of_equiv (innAutEquiv (L2.equivPSL F).symm).symm
      (psl2_odd_hasDihedralSylowTwo_model F hodd)
  refine ⟨?_, ?_⟩
  · obtain ⟨m, hm, ⟨d⟩⟩ := hdihD (M.toSylow hS)
    refine ⟨m, hm, ⟨?_⟩⟩
    exact (Subgroup.subgroupOfEquivOfLe hS.1).symm.trans
      ((MulEquiv.subgroupCongr (M.coe_toSylow hS).symm).trans d)
  · obtain ⟨m, hm, ⟨d⟩⟩ := hdihN (M.toSylow hSN)
    have hncD : ¬ IsCyclic ↥(M.toSylow hSN) := by
      intro hcyc
      have hc := d.isCyclic.mp hcyc
      exact DihedralGroup.not_isCyclic (n := 2 ^ m) (fun h => by
        have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
        omega) hc
    intro hcyc
    apply hncD
    have e1 : ↥((innAut (PSL2 F)).subgroupOf S) ≃* ↥(S ⊓ innAut (PSL2 F)) := by
      have h1 : (innAut (PSL2 F)).subgroupOf S = (S ⊓ innAut (PSL2 F)).subgroupOf S := by
        rw [inf_comm, Subgroup.inf_subgroupOf_right]
      exact (MulEquiv.subgroupCongr h1).trans (Subgroup.subgroupOfEquivOfLe inf_le_left)
    have e2 : ↥(S ⊓ innAut (PSL2 F)) ≃* ↥(M.toSylow hSN) :=
      (Subgroup.subgroupOfEquivOfLe hSN.1).symm.trans
        (MulEquiv.subgroupCongr (M.coe_toSylow hSN).symm)
    exact (e1.trans e2).isCyclic.mp hcyc

end DihData

section QLevel

variable {F : Type} [Field F] [Finite F]

theorem sl_sylow_pair_conj (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    {Q : Type} [Group Q] [Finite Q] (e : Q ≃* SpecialLinearGroup (Fin 2) F) {α : MulAut Q}
    (hα2 : α * α = 1) (hαin : α ∉ innOf Q)
    (hαf : (gammaOf hodd h3 (MulAut.congr e α)).right = 1)
    (P₁ P₂ : Sylow 2 Q) (h₁ : ∀ x ∈ (P₁ : Subgroup Q), α x ∈ (P₁ : Subgroup Q))
    (h₂ : ∀ x ∈ (P₂ : Subgroup Q), α x ∈ (P₂ : Subgroup Q)) :
    ∃ g : Q, MulAut.conj g * α = α * MulAut.conj g ∧
      ∀ y, y ∈ (P₁ : Subgroup Q) ↔ g * y * g⁻¹ ∈ (P₂ : Subgroup Q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL2 : L2Field F := ⟨hodd, h3⟩
  let ι : MulAut Q →* MulAut (PSL2 F) := psl2AutHom.comp (MulAut.congr e).toMonoidHom
  have hι : Function.Injective ι :=
    (psl2AutHom_injective hodd h3).comp (MulAut.congr e).injective
  let π : Q →* PSL2 F :=
    (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))).comp e.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hιconj : ∀ x : Q, ι (MulAut.conj x) = MulAut.conj (π x) := by
    intro x
    show psl2AutHom (MulAut.congr e (MulAut.conj x)) = _
    rw [congr_conj, psl2AutHom_conj]
    rfl
  let e₀ : PSL2 F ≃* L2 F := (L2.equivPSL F).symm
  let ρ : Q →* MulAut (PSL2 F) := (MulAut.conj : PSL2 F →* MulAut (PSL2 F)).comp π
  have hρι : ∀ x, ρ x = ι (MulAut.conj x) := fun x => (hιconj x).symm
  have hker : ∀ y, ρ y = 1 → ∀ P : Sylow 2 Q, y ∈ (P : Subgroup Q) := by
    intro y hy P
    have h1 : π y = 1 := by
      apply conj_injective_of_L2 e₀
      rw [map_one]
      exact hy
    have h2 : e y ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
      have : (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))) (e y) = 1 := h1
      exact (QuotientGroup.eq_one_iff _).1 this
    have hy2 : y * y = 1 := by
      apply e.injective
      rw [map_mul, map_one]
      exact sq_eq_one_of_mem_center_sl2 h2
    have hyc : ∀ a : Q, y * a = a * y := fun a => by
      apply e.injective
      rw [map_mul, map_mul]
      exact (Subgroup.mem_center_iff.1 h2 (e a)).symm
    have hP2 : IsPGroup 2 ↥((P : Subgroup Q) ⊔ zpowers y) :=
      isPGroup_sup_zpowers_of_involution P.isPGroup' hy2 (fun a ha => by
        have : y * a * y⁻¹ = a := by rw [hyc a]; group
        rw [this]
        exact ha)
    have := P.is_maximal' hP2 le_sup_left
    rw [← this]
    exact mem_sup_right (mem_zpowers y)
  have hρP : ∀ (P : Sylow 2 Q) y, ρ y ∈ (P : Subgroup Q).map ρ ↔ y ∈ (P : Subgroup Q) := by
    intro P y
    constructor
    · rintro ⟨y', hy', hρ'⟩
      have hk : y'⁻¹ * y ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hρ', inv_mul_cancel]
      have h2 := hker _ hk P
      have : y = y' * (y'⁻¹ * y) := by group
      rw [this]
      exact mul_mem hy' h2
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hN : innAut (PSL2 F) = (⊤ : Subgroup Q).map ρ := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨k, rfl⟩ := hπ u
      exact ⟨k, trivial, rfl⟩
    · rintro ⟨k, -, rfl⟩
      exact ⟨π k, rfl⟩
  have hsyl : ∀ P : Sylow 2 Q, M.Syl2In ((P : Subgroup Q).map ρ) (innAut (PSL2 F)) := by
    intro P
    rw [hN]
    refine ⟨Subgroup.map_mono le_top, P.isPGroup'.map ρ, ?_⟩
    rw [Subgroup.relIndex_map_map, top_sup_eq]
    have hprod := Subgroup.relIndex_mul_relIndex (H := (P : Subgroup Q))
      (K := (P : Subgroup Q) ⊔ ρ.ker) (L := ⊤) le_sup_left le_top
    have hodd' : ¬ 2 ∣ (P : Subgroup Q).relIndex ⊤ := by
      rw [Subgroup.relIndex_top_right]
      exact P.not_dvd_index
    intro h2
    exact hodd' (h2.trans (Dvd.intro_left _ hprod))
  have hα₀D : ι α ∈ innDiagSub e₀ := by
    rw [mem_innDiagSub_iff]
    show fieldProj e₀ (psl2AutHom (MulAut.congr e α)) = 1
    rw [fieldProj_psl2AutHom hodd h3]
    exact hαf
  have hα₀N : ι α ∉ innAut (PSL2 F) := by
    intro hmem
    obtain ⟨u, hu⟩ := hmem
    obtain ⟨k, rfl⟩ := hπ u
    apply hαin
    refine ⟨k, ?_⟩
    apply hι
    rw [hιconj, hu]
  have hα₀2 : ι α * ι α = 1 := by rw [← map_mul, hα2, map_one]
  have hND : innAut (PSL2 F) ≤ innDiagSub e₀ := innAut_le_innDiagSub e₀
  have hN2 : (innAut (PSL2 F)).relIndex (innDiagSub e₀) = 2 := innAut_relIndex_two e₀ hL2
  have hstab : ∀ P : Sylow 2 Q, (∀ x ∈ (P : Subgroup Q), α x ∈ (P : Subgroup Q)) →
      ∀ x ∈ (P : Subgroup Q).map ρ, ι α * x * (ι α)⁻¹ ∈ (P : Subgroup Q).map ρ := by
    rintro P hP _ ⟨y, hy, rfl⟩
    refine ⟨α y, hP y hy, ?_⟩
    rw [hρι, hρι, ← map_inv, ← map_mul, ← map_mul, mulAut_conj_conj]
  have hsylD : ∀ P : Sylow 2 Q, (∀ x ∈ (P : Subgroup Q), α x ∈ (P : Subgroup Q)) →
      ∃ S : Subgroup (MulAut (PSL2 F)), M.Syl2In S (innDiagSub e₀) ∧
        (P : Subgroup Q).map ρ ⊔ zpowers (ι α) ≤ S := by
    intro P hP
    have hT2 := isPGroup_sup_zpowers_of_involution (hsyl P).2.1 hα₀2 (hstab P hP)
    exact M.exists_syl2In_ge hT2 (sup_le ((hsyl P).1.trans hND) (zpowers_le.2 hα₀D))
  obtain ⟨S₁, hS₁, hTS₁⟩ := hsylD P₁ h₁
  obtain ⟨S₂, hS₂, hTS₂⟩ := hsylD P₂ h₂
  have hSN : ∀ (P : Sylow 2 Q) (S : Subgroup (MulAut (PSL2 F))), M.Syl2In S (innDiagSub e₀) →
      (P : Subgroup Q).map ρ ⊔ zpowers (ι α) ≤ S →
      S ⊓ innAut (PSL2 F) = (P : Subgroup Q).map ρ := by
    intro P S hS hTS
    exact M.Syl2In.eq_of_le (hsyl P) hS.2.1.to_inf_left
      (le_inf (le_sup_left.trans hTS) (hsyl P).1) inf_le_right
  have hS₁N := hSN P₁ S₁ hS₁ hTS₁
  have hS₂N := hSN P₂ S₂ hS₂ hTS₂
  obtain ⟨⟨m, hm, ⟨e₂⟩⟩, hnc⟩ := dihedral_data_PSL hL2 hS₁ (by rw [hS₁N]; exact hsyl P₁)
  have hα₁S : ι α ∈ S₁ := hTS₁ (mem_sup_right (mem_zpowers _))
  have hα₂S : ι α ∈ S₂ := hTS₂ (mem_sup_right (mem_zpowers _))
  obtain ⟨h, hhN, hhα, hhS⟩ := outer_sylow_conj_aux (innDiagSub e₀) (innAut (PSL2 F)) hN2 hα₀D
    hα₀N hα₀2 hS₂ hS₁ hα₂S hα₁S hm e₂ hnc
  obtain ⟨u, rfl⟩ := hhN
  obtain ⟨k, rfl⟩ := hπ u
  refine ⟨k, ?_, fun y => ?_⟩
  · have h1 : ι (MulAut.conj k * α * (MulAut.conj k)⁻¹) = ι α := by
      rw [map_mul, map_mul, map_inv, hιconj]
      exact hhα
    have h2 := hι h1
    calc MulAut.conj k * α = (MulAut.conj k * α * (MulAut.conj k)⁻¹) * MulAut.conj k := by group
      _ = α * MulAut.conj k := by rw [h2]
  · have hρk : MulAut.conj (π k) * ρ y * (MulAut.conj (π k))⁻¹ = ρ (k * y * k⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      rfl
    have hmemN : ρ (k * y * k⁻¹) ∈ innAut (PSL2 F) := by
      rw [hN]
      exact ⟨_, trivial, rfl⟩
    have hmemN' : ρ y ∈ innAut (PSL2 F) := by
      rw [hN]
      exact ⟨_, trivial, rfl⟩
    constructor
    · intro hy
      have h1 : ρ y ∈ S₁ := le_sup_left.trans hTS₁ ⟨y, hy, rfl⟩
      have h2 := (hhS _).1 h1
      rw [hρk] at h2
      have h3' : ρ (k * y * k⁻¹) ∈ S₂ ⊓ innAut (PSL2 F) := ⟨h2, hmemN⟩
      rw [hS₂N] at h3'
      exact (hρP P₂ _).1 h3'
    · intro hy
      have h1 : ρ (k * y * k⁻¹) ∈ S₂ := le_sup_left.trans hTS₂ ⟨_, hy, rfl⟩
      rw [← hρk] at h1
      have h2 := (hhS _).2 h1
      have h3' : ρ y ∈ S₁ ⊓ innAut (PSL2 F) := ⟨h2, hmemN'⟩
      rw [hS₁N] at h3'
      exact (hρP P₁ _).1 h3'

end QLevel

section PairIso

variable {F : Type} [Field F] [Finite F]

theorem mulAut_congr_conj {Q Q' : Type} [Group Q] [Group Q'] (η : Q ≃* Q') (x : Q) :
    MulAut.congr η (MulAut.conj x) = MulAut.conj (η x) := by
  ext z
  simp [MulAut.conj_apply]

theorem exists_sylow_map_equiv {Q Q' : Type} [Group Q] [Group Q'] [Finite Q] [Finite Q'] (η : Q ≃* Q')
    (P : Sylow 2 Q) : ∃ P₁ : Sylow 2 Q', ∀ y, y ∈ (P₁ : Subgroup Q') ↔ η.symm y ∈ (P : Subgroup Q) := by
  have hf : Function.Surjective η.toMonoidHom := η.surjective
  refine ⟨P.mapSurjective hf, fun y => ?_⟩
  rw [Sylow.coe_mapSurjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : η.symm (η.toMonoidHom x) = x := by simp
    rw [this]
    exact hx
  · intro hy
    exact ⟨η.symm y, hy, by simp⟩

omit [Finite F] in
theorem sl_sylow_iso {Q Q' : Type} [Group Q] [Group Q'] [Finite Q] [Finite Q']
    (e : Q ≃* SpecialLinearGroup (Fin 2) F) (e' : Q' ≃* SpecialLinearGroup (Fin 2) F)
    (P : Sylow 2 Q) (P' : Sylow 2 Q') :
    ∃ η : Q ≃* Q', ∀ x, x ∈ (P : Subgroup Q) ↔ η x ∈ (P' : Subgroup Q') := by
  classical
  let η₀ : Q ≃* Q' := e.trans e'.symm
  obtain ⟨P₁, hP₁⟩ := exists_sylow_map_equiv η₀ P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q' P₁ P'
  refine ⟨η₀.trans (MulAut.conj g), fun x => ?_⟩
  have h := congrArg (fun S : Sylow 2 Q' => (S : Subgroup Q')) hg
  simp only [Sylow.coe_subgroup_smul] at h
  have h2 : ∀ y, y ∈ (P' : Subgroup Q') ↔ g⁻¹ * y * g ∈ (P₁ : Subgroup Q') := fun y => by
    rw [← h, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  show x ∈ (P : Subgroup Q) ↔ (MulAut.conj g) (η₀ x) ∈ (P' : Subgroup Q')
  rw [h2, hP₁]
  simp [MulAut.conj_apply, mul_assoc]

theorem sl_pair_iso (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    {Q Q' : Type} [Group Q] [Group Q'] [Finite Q] [Finite Q']
    (e : Q ≃* SpecialLinearGroup (Fin 2) F) (e' : Q' ≃* SpecialLinearGroup (Fin 2) F)
    {α : MulAut Q} {α' : MulAut Q'} (hα2 : α * α = 1) (hα'2 : α' * α' = 1)
    (hαin : α ∉ innOf Q) (hα'in : α' ∉ innOf Q')
    (hαf : (gammaOf hodd h3 (MulAut.congr e α)).right = 1)
    (hα'f : (gammaOf hodd h3 (MulAut.congr e' α')).right = 1)
    (P : Sylow 2 Q) (P' : Sylow 2 Q')
    (hP : ∀ x ∈ (P : Subgroup Q), α x ∈ (P : Subgroup Q))
    (hP' : ∀ x ∈ (P' : Subgroup Q'), α' x ∈ (P' : Subgroup Q')) :
    ∃ η : Q ≃* Q', (∀ x, η (α x) = α' (η x)) ∧
      ∀ x, x ∈ (P : Subgroup Q) ↔ η x ∈ (P' : Subgroup Q') := by
  classical
  let η₀ : Q ≃* Q' := e.trans e'.symm
  let ᾱ : MulAut Q' := MulAut.congr η₀ α
  have hᾱ2 : ᾱ * ᾱ = 1 := by rw [← map_mul, hα2, map_one]
  have hᾱin : ᾱ ∉ innOf Q' := by
    rintro ⟨u, hu⟩
    apply hαin
    refine ⟨η₀.symm u, ?_⟩
    apply (MulAut.congr η₀).injective
    rw [mulAut_congr_conj, MulEquiv.apply_symm_apply]
    exact hu
  have hfield : MulAut.congr e' ᾱ = MulAut.congr e α := by
    ext x
    simp [ᾱ, η₀]
  have hᾱf : (gammaOf hodd h3 (MulAut.congr e' ᾱ)).right = 1 := by
    rw [hfield]
    exact hαf
  obtain ⟨k, hk⟩ := sl_outer_conj hodd h3 e' hᾱ2 hα'2 hᾱin hα'in hᾱf hα'f
  let η₁ : Q ≃* Q' := η₀.trans (MulAut.conj k)
  have hconjα : ∀ y, α' y = k * ᾱ (k⁻¹ * y * k) * k⁻¹ := by
    intro y
    have := congrArg (fun f : MulAut Q' => f y) hk
    simpa [MulAut.conj_apply] using this.symm
  have hᾱx : ∀ x, ᾱ (η₀ x) = η₀ (α x) := fun x => by simp [ᾱ]
  have hη₁α : ∀ x, η₁ (α x) = α' (η₁ x) := by
    intro x
    rw [hconjα]
    have h1 : k⁻¹ * η₁ x * k = η₀ x := by
      show k⁻¹ * (k * η₀ x * k⁻¹) * k = η₀ x
      group
    rw [h1, hᾱx]
    rfl
  obtain ⟨P₁, hP₁⟩ := exists_sylow_map_equiv η₁ P
  have hinv : ∀ y ∈ (P₁ : Subgroup Q'), α' y ∈ (P₁ : Subgroup Q') := by
    intro y hy
    rw [hP₁] at hy ⊢
    have h1 : η₁.symm (α' y) = α (η₁.symm y) := by
      apply η₁.injective
      rw [MulEquiv.apply_symm_apply, hη₁α, MulEquiv.apply_symm_apply]
    rw [h1]
    exact hP _ hy
  obtain ⟨g, hg, hgP⟩ := sl_sylow_pair_conj hodd h3 e' hα'2 hα'in hα'f P₁ P' hinv hP'
  refine ⟨η₁.trans (MulAut.conj g), fun x => ?_, fun x => ?_⟩
  · have h1 : (MulAut.conj g * α') (η₁ x) = (α' * MulAut.conj g) (η₁ x) := by rw [hg]
    show g * η₁ (α x) * g⁻¹ = α' (g * η₁ x * g⁻¹)
    rw [hη₁α]
    simpa [MulAut.conj_apply] using h1
  · show x ∈ (P : Subgroup Q) ↔ g * η₁ x * g⁻¹ ∈ (P' : Subgroup Q')
    rw [← hgP, hP₁]
    simp

end PairIso

end CFSG.GH74.GLS.IVK.Lifted
