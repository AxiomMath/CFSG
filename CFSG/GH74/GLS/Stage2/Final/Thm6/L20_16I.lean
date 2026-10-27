module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_15
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_16Tr
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAut

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L20

open Subgroup CFSG CFSG.LocalCores CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GorensteinWalter
open scoped commutatorElement

section IStruct

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}

theorem exists_psl2_map {L : Type} [Group L] {F : Type} [Field F]
    (e : L ≃* CFSG.Assembly.LowTwoRank.StatedSL 2 F) :
    ∃ θ₀ : L →* PSL2 F, Function.Surjective θ₀ ∧ ∀ x : L, θ₀ x = 1 ↔ ∀ l : L, x * l = l * x := by
  let ε : L ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  refine ⟨(QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp ε.toMonoidHom, ?_, ?_⟩
  · intro p
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective p
    exact ⟨ε.symm s, by simp⟩
  · intro x
    show QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) (ε x) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    constructor
    · intro hc l
      have := hc (ε l)
      apply ε.injective
      rw [map_mul, map_mul]
      exact this.symm
    · intro hc s
      obtain ⟨l, rfl⟩ := ε.surjective s
      rw [← map_mul, ← map_mul, hc l]

theorem zbar_ne_one (hz2 : z * z = 1) (hz1' : z ≠ 1) : toBar z ⟨z, mem_Cen_self z⟩ ≠ 1 := by
  intro h1
  have h2 : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := by
    have := (QuotientGroup.eq_one_iff (N := pPrimeCore 2 ↥(Cen z)) (⟨z, mem_Cen_self z⟩ : ↥(Cen z))).mp h1
    exact this
  have hodd : Odd (orderOf (⟨z, mem_Cen_self z⟩ : ↥(Cen z))) := by
    have hd : orderOf (⟨⟨z, mem_Cen_self z⟩, h2⟩ : ↥(pPrimeCore 2 ↥(Cen z))) ∣
        Nat.card ↥(pPrimeCore 2 ↥(Cen z)) := orderOf_dvd_natCard _
    have hodd' : Odd (Nat.card ↥(pPrimeCore 2 ↥(Cen z))) :=
      Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))
    have h1' := Odd.of_dvd_nat hodd' hd
    rwa [Subgroup.orderOf_mk] at h1'
  have hord : orderOf (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) = 2 := by
    rw [Subgroup.orderOf_mk]; exact orderOf_eq_prime (by rw [sq]; exact hz2) hz1'
  rw [hord] at hodd
  exact absurd hodd (by decide)

theorem inf_bar_cases (h : Stage1Pair G z S q L₁ L₂) (hz2 : z * z = 1) (hz1' : z ≠ 1)
    {w : CentralizerBar z} (hw : w ∈ L₁ ⊓ L₂) : w = 1 ∨ w = toBar z ⟨z, mem_Cen_self z⟩ := by
  have hP := PairShape.of_stage1Pair h
  have hzc := Subgroup.mem_center_iff.mp (toBar_z_mem_center z)
  have hzmem := center_of_pair h (w := toBar z ⟨z, mem_Cen_self z⟩)
    (mem_sup_of_centralizes hP (fun a _ => (hzc a).symm) (fun a _ => (hzc a).symm))
    (fun a _ => (hzc a).symm) (fun a _ => (hzc a).symm)
  have hz1 := zbar_ne_one hz2 hz1'
  by_cases hx1 : w = 1
  · exact Or.inl hx1
  · right
    have hcard : Nat.card ↥(L₁ ⊓ L₂) = 2 := h.prod.2.2
    obtain ⟨t, ht, huniq⟩ := (Nat.card_eq_two_iff' (⟨1, (L₁ ⊓ L₂).one_mem⟩ : ↥(L₁ ⊓ L₂))).mp hcard
    have h1 := huniq ⟨w, hw⟩ (fun e => hx1 (congrArg Subtype.val e))
    have h2 := huniq ⟨toBar z ⟨z, mem_Cen_self z⟩, hzmem⟩ (fun e => hz1 (congrArg Subtype.val e))
    exact congrArg Subtype.val (h1.trans h2.symm)

omit [Finite G] in
theorem diag_mem_odd (hz2 : z * z = 1) {y : G} (hyC : y ∈ Cen z) {a : G} (haC : a ∈ Cen z)
    (hcase : toBar z ⟨a, haC⟩ = 1 ∨ toBar z ⟨a, haC⟩ = toBar z ⟨z, mem_Cen_self z⟩) :
    a * (y * a * y⁻¹) ∈ OddCore z := by
  rcases hcase with h1 | h1
  · have hmem : (⟨a, haC⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := (QuotientGroup.eq_one_iff _).mp h1
    have haA : a ∈ OddCore z := ⟨⟨a, haC⟩, hmem, rfl⟩
    exact (OddCore z).mul_mem haA (OddCore_norm z hyC haA)
  · obtain ⟨c, rfl⟩ : ∃ c, a = z * c := ⟨z * a, by rw [← mul_assoc, hz2, one_mul]⟩
    have hmem : (⟨z * c, haC⟩ : ↥(Cen z))⁻¹ * ⟨z, mem_Cen_self z⟩ ∈ pPrimeCore 2 ↥(Cen z) :=
      QuotientGroup.eq.mp h1
    have hb : (z * c)⁻¹ * z ∈ OddCore z := ⟨_, hmem, rfl⟩
    have hcinv : c⁻¹ ∈ OddCore z := by
      have e : (z * c)⁻¹ * z = c⁻¹ := by group
      rwa [e] at hb
    have hcA : c ∈ OddCore z := by simpa using (OddCore z).inv_mem hcinv
    have hcC : c ∈ Cen z := OddCore_le_Cen z hcA
    have hzc : z * c = c * z := (Subgroup.mem_centralizer_singleton_iff.mp hcC).symm
    have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    have e : (z * c) * (y * (z * c) * y⁻¹) = c * (y * c * y⁻¹) := by
      calc (z * c) * (y * (z * c) * y⁻¹) = (z * c) * ((y * z) * c * y⁻¹) := by group
        _ = (z * c) * ((z * y) * c * y⁻¹) := by rw [hyz]
        _ = (z * c * z) * (y * c * y⁻¹) := by group
        _ = (c * z * z) * (y * c * y⁻¹) := by rw [hzc]
        _ = c * (y * c * y⁻¹) := by rw [mul_assoc c z z, hz2, mul_one]
    rw [e]
    exact (OddCore z).mul_mem hcA (OddCore_norm z hyC hcA)

theorem I_struct (h : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hz2 : z * z = 1) (hz1' : z ≠ 1)
    {y : G} (hyC : y ∈ Cen z) (hy2 : y * y = 1) (hsw : cj (toBar z ⟨y, hyC⟩) L₁ = L₂) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ψ : ↥(Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G))) →* PSL2 F),
      IsOddPrimePower (Nat.card F) ∧ Function.Surjective ψ ∧
      ∀ w, ψ w = 1 → (∀ v, v * w = w * v) ∧ Odd (orderOf w) := by
  have hP := PairShape.of_stage1Pair h
  set I := Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)) with hI
  obtain ⟨F, hFf, hFfin, hq, ⟨e⟩⟩ := h.sl₁
  have hqF : Nat.card F = q := hq
  obtain ⟨θ₀, hθ₀s, hθ₀k⟩ := exists_psl2_map e
  have hmem : ∀ a : ↥K₁, toBar z (Subgroup.inclusion hK.le₁ a) ∈ L₁ := fun a => by
    have : toBar z (Subgroup.inclusion hK.le₁ a) ∈ barOf z K₁ := ⟨Subgroup.inclusion hK.le₁ a, a.2, rfl⟩
    rwa [hK.bar₁] at this
  let π₁ : ↥K₁ →* ↥L₁ := ((toBar z).comp (Subgroup.inclusion hK.le₁)).codRestrict L₁ hmem
  have hπ₁ : ∀ a : ↥K₁, ((π₁ a : ↥L₁) : CentralizerBar z) = toBar z (Subgroup.inclusion hK.le₁ a) :=
    fun a => rfl
  have hπ₁s : Function.Surjective π₁ := by
    intro l
    have hl : (l : CentralizerBar z) ∈ barOf z K₁ := by rw [hK.bar₁]; exact l.2
    obtain ⟨k', hk', hkl⟩ := hl
    exact ⟨⟨k', hk'⟩, Subtype.ext hkl⟩
  let θ : ↥K₁ →* PSL2 F := θ₀.comp π₁
  obtain ⟨hs₁, hs₂⟩ := hK.swap y hyC hsw
  let δ := diagHom K₁ K₂ y hs₁ hK.comm
  have hδI : ∀ a : ↥K₁, δ a ∈ I := fun a => diag_le_layer hK.quasi₁ hK.comm hy2 hs₁ hs₂ ⟨a, rfl⟩
  let d' : ↥K₁ →* ↥I := δ.codRestrict I hδI
  have hd'val : ∀ a : ↥K₁, ((d' a : ↥I) : G) = (a : G) * (y * a * y⁻¹) := fun a => rfl
  have hIKK : I ≤ K₁ ⊔ K₂ := (Em_le _).trans inf_le_left
  have hIy : ∀ p ∈ I, y * p * y⁻¹ = p := by
    intro p hp
    have h1 : p ∈ centralizer ({y} : Set G) :=
      (inf_le_right : (K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G) ≤ _) (Em_le _ hp)
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp h1
    calc y * p * y⁻¹ = (y * p) * y⁻¹ := rfl
      _ = (p * y) * y⁻¹ := by rw [← h2]
      _ = p := by group
  have hd's : Function.Surjective d' := by
    intro w
    have hw : (w : G) ∈ δ.range :=
      perfect_le_diag hK.comm hs₁ hs₂ (Em_perfect _) hIKK hIy w.2
    obtain ⟨a, ha⟩ := hw
    exact ⟨a, Subtype.ext ha⟩
  have hker : d'.ker ≤ θ.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    have h1 : (a : G) * (y * a * y⁻¹) = 1 := congrArg Subtype.val ha
    have h2 : (a : G) ∈ K₂ := by
      have : (a : G) = (y * a * y⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]; exact K₂.inv_mem (hs₁ a a.2)
    have h3 : (π₁ a : CentralizerBar z) ∈ L₂ := by
      have : toBar z (Subgroup.inclusion hK.le₂ ⟨a, h2⟩) ∈ barOf z K₂ :=
        ⟨Subgroup.inclusion hK.le₂ ⟨a, h2⟩, h2, rfl⟩
      rwa [hK.bar₂] at this
    show θ₀ (π₁ a) = 1
    rw [hθ₀k]
    intro l
    exact Subtype.ext (hP.comm l l.2 _ h3).symm
  let ψ : ↥I →* PSL2 F :=
    (MonoidHom.liftOfRightInverse d' (Function.surjInv hd's) (Function.rightInverse_surjInv hd's)) ⟨θ, hker⟩
  have hψd : ∀ a : ↥K₁, ψ (d' a) = θ a := fun a =>
    MonoidHom.liftOfRightInverse_comp_apply d' (Function.surjInv hd's) (Function.rightInverse_surjInv hd's)
      ⟨θ, hker⟩ a
  have hψs : Function.Surjective ψ := by
    have : Function.Surjective (ψ ∘ d') := by
      have e' : (ψ ∘ d') = θ := funext hψd
      rw [e']
      exact hθ₀s.comp hπ₁s
    exact Function.Surjective.of_comp this
  refine ⟨F, hFf, hFfin, ψ, ?_, hψs, ?_⟩
  · have hodd : Odd (Nat.card F) := by rw [hqF]; exact h.odd
    exact CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hodd
  · intro w hw
    obtain ⟨a, rfl⟩ := hd's w
    rw [hψd] at hw
    have hc : ∀ l : ↥L₁, (π₁ a) * l = l * (π₁ a) := (hθ₀k _).mp hw
    have hmL₂ : (π₁ a : CentralizerBar z) ∈ L₂ := by
      have := center_of_pair h (w := (π₁ a : CentralizerBar z)) (Subgroup.mem_sup_left (π₁ a).2)
        (fun x hx => congrArg Subtype.val (hc ⟨x, hx⟩)) (fun x hx => hP.comm _ (π₁ a).2 x hx)
      exact this.2
    have hcase := inf_bar_cases h hz2 hz1' (w := (π₁ a : CentralizerBar z)) ⟨(π₁ a).2, hmL₂⟩
    have haC : (a : G) ∈ Cen z := hK.le₁ a.2
    have hAmem : ((d' a : ↥I) : G) ∈ OddCore z := by
      rw [hd'val]
      refine diag_mem_odd hz2 hyC haC ?_
      rcases hcase with h1 | h1
      · left; rw [hπ₁] at h1; exact h1
      · right; rw [hπ₁] at h1; exact h1
    refine ⟨fun v => ?_, ?_⟩
    · have hvL : (v : G) ∈ Em (Cen z) := by
        rw [hK.layer]; exact hIKK v.2
      exact Subtype.ext (hK.oddcomm _ hAmem _ hvL).symm
    · have : Odd (orderOf ((d' a : ↥I) : G)) := by
        obtain ⟨b, hb, hbe⟩ := hAmem
        rw [← hbe]
        have := odd_orderOf_of_mem_pPrimeCore hb
        rwa [← Subgroup.orderOf_coe] at this
      rwa [Subgroup.orderOf_coe] at this

theorem I_facts (h : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hz2 : z * z = 1) (hz1' : z ≠ 1)
    {y : G} (hyC : y ∈ Cen z) (hy2 : y * y = 1) (hsw : cj (toBar z ⟨y, hyC⟩) L₁ = L₂) :
    (∃ x₁ ∈ Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)), ∃ x₂ ∈ Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)),
      x₁ * x₁ = 1 ∧ x₂ * x₂ = 1 ∧ x₁ * x₂ = x₂ * x₁ ∧ x₁ ≠ 1 ∧ x₂ ≠ 1 ∧ x₁ ≠ x₂) ∧
    (∀ a ∈ Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)), ∀ b ∈ Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)),
      a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 →
        ∃ c ∈ Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)), c * a * c⁻¹ = b) ∧
    (∀ w ∈ Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)),
      (∀ v ∈ Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)), v * w = w * v) → w * w = 1 → w = 1) := by
  obtain ⟨F, _, _, ψ, hF, hs, hk⟩ := I_struct h hK hz2 hz1' hyC hy2 hsw
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, c, ha2, hc2, hac, ha1, hc1, hne⟩ := tr_four hF ψ hk hs
    exact ⟨a, a.2, c, c.2, congrArg Subtype.val ha2, congrArg Subtype.val hc2, congrArg Subtype.val hac,
      fun h' => ha1 (Subtype.ext h'), fun h' => hc1 (Subtype.ext h'), fun h' => hne (Subtype.ext h')⟩
  · intro a ha b hb ha2 hb2 ha1 hb1
    obtain ⟨c, hc⟩ := tr_conj hF ψ hk hs (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (Subtype.ext ha2) (Subtype.ext hb2)
      (fun h' => ha1 (congrArg Subtype.val h')) (fun h' => hb1 (congrArg Subtype.val h'))
    exact ⟨c, c.2, congrArg Subtype.val hc⟩
  · intro w hw hwc hw2
    have := tr_center ψ hk hs (w := ⟨w, hw⟩) (fun v => Subtype.ext (hwc v v.2)) (Subtype.ext hw2)
    exact congrArg Subtype.val this

end IStruct

end CFSG.GH74.GLS.Stage2.Final.Thm6.L20
