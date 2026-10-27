module

public import CFSG.GH74.Generic.S1.Exo.Q3HSLevel
public import CFSG.GH74.KGroups.M11

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Filter.ClassicalOdd CFSG.Assembly CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {c y : H} {JA JB : Subgroup H}

theorem perfect_aut_eq_one {G : Type} [Group G] (hG : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) (α : MulAut G)
    (hα : ∀ g : G, (QuotientGroup.mk (α g) : G ⧸ center G) = QuotientGroup.mk g) : α = 1 := by
  have hz : ∀ g : G, g⁻¹ * α g ∈ center G := fun g => QuotientGroup.eq.1 (hα g).symm
  have hcomm : ∀ a b : G, α ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    obtain ⟨z₁, hz₁⟩ : ∃ z₁ ∈ center G, α a = a * z₁ := ⟨a⁻¹ * α a, hz a, by group⟩
    obtain ⟨z₂, hz₂, h2⟩ : ∃ z₂ ∈ center G, α b = b * z₂ := ⟨b⁻¹ * α b, hz b, by group⟩
    rw [map_commutatorElement, hz₁.2, h2, commutator_mul_central a b z₁ z₂ hz₁.1 hz₂]
  let L : Subgroup G := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id G)
  have hL : (⊤ : Subgroup G) ≤ L := by
    rw [← hG, Subgroup.commutator_le]
    intro a _ b _
    exact hcomm a b
  ext g
  exact hL (Subgroup.mem_top g)

theorem q8_nonid_sq : ∀ q : Q8, q ≠ 1 → q ≠ QuaternionGroup.a 2 → q * q = QuaternionGroup.a 2 := by decide

theorem q8_nonid_cases : ∀ q : Q8, q ≠ 1 → (q = QuaternionGroup.a 2 ∨ q * q = QuaternionGroup.a 2) := by decide

theorem q3_hZ (h : Nbhd3Hyp H c y JA JB) {N : Subgroup H} [N.Normal] {ψA : Q8 →* H}
    (hAm : ∀ g, ψA g ∈ JA) (hAz : ψA (QuaternionGroup.a 2) = c)
    (hcommA : ∀ q : Q8, ∀ n ∈ N, ψA q * n = n * ψA q) :
    ∀ q : Q8, ψA q ∈ N → q = 1 ∨ q = QuaternionGroup.a 2 := by
  intro q hqN
  by_contra hne
  push Not at hne
  have hsq := q8_nonid_sq q hne.1 hne.2
  have hg2 : (ψA q) ^ 2 ≠ 1 := by
    rw [pow_two, ← map_mul, hsq, hAz]
    exact h.c_ne_one
  have hg4 : (ψA q) ^ 4 = 1 := by
    rw [← map_pow, q8_pow_four, map_one]
  obtain ⟨k, hkA, hk⟩ := sl23_noncomm_conj h.sl2A (hAm q) hg2 hg4
  apply hk
  have hconj : k * ψA q * k⁻¹ ∈ N := Subgroup.Normal.conj_mem ‹N.Normal› _ hqN k
  exact hcommA q _ hconj

theorem center_eq_bot_of_simple_nonab {G : Type} [Group G] [IsSimpleGroup G]
    (hn : ∃ a b : G, a * b ≠ b * a) : center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)

theorem nonab_of_simple_card {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hno
  push Not at hno
  let _ : CommGroup G := { ‹Group G› with mul_comm := fun a b => hno a b }
  exact h IsSimpleGroup.prime_card

theorem q3_caseII (hR : RankTwoStmt)
    (h : Nbhd3Hyp H c y JA JB) {N : Subgroup H} {ψA ψB : Q8 →* H}
    (hr : Q3Red H c y JA JB N ψA ψB) (hII : ∀ g, ψA g ∈ CFSG.pCore 2 H)
    {u : H} (hu : u * u = 1) {P : Subgroup H} (hPs : IsSimpleGroup ↥P) (hP360 : Nat.card ↥P = 360)
    (hPl : P ≤ layer H) (hPu : P ≤ centralizer ({u} : Set H))
    (hmax : ∀ M : Subgroup H, ⁅M, M⁆ = M → M ≤ centralizer ({u} : Set H) → M ≤ P) : False := by
  classical
  have : (layer H).Characteristic := CFSG.LocalCores.layer_characteristic
  have hNn : N.Normal := by rw [← hr.layer_eq]; infer_instance
  have := hNn
  have hPN : P ≤ N := hr.layer_eq ▸ hPl
  have hqs : CFSG.IsQuasisimple ↥N := hr.comp.1
  have hSsimple : IsSimpleGroup (↥N ⧸ center ↥N) := hqs.2.1
  have hnonab : ∃ a b : ↥N ⧸ center ↥N, a * b ≠ b * a := hqs.2.2
  have hcommA : ∀ q : Q8, ∀ n ∈ N, ψA q * n = n * ψA q := fun q n hn =>
    (Subgroup.mem_centralizer_iff.1 (pCore_two_le_centralizer_layer (hII q)) n (hr.layer_eq ▸ hn)).symm
  have hZ := q3_hZ h hr.mem_JA hr.zA hcommA
  let π : ↥N →* ↥N ⧸ center ↥N := QuotientGroup.mk' (center ↥N)
  let ψB' : Q8 →* ↥N := ψB.codRestrict N hr.B_mem
  let ψ : Q8 →* ↥N ⧸ center ↥N := π.comp ψB'
  have hyN : y ∈ N := hr.zB ▸ hr.B_mem _
  have hNperf : ⁅N, N⁆ = N := Subgroup.isPerfect_iff.mp hqs.1
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    by_contra hg1
    have hgc : ψB' g ∈ center ↥N := (QuotientGroup.eq_one_iff _).1 hg
    have hyc : (⟨y, hyN⟩ : ↥N) ∈ center ↥N := by
      rcases q8_nonid_cases g hg1 with h1 | h1
      · have : ψB' g = ⟨y, hyN⟩ := Subtype.ext (by simp [ψB', h1, hr.zB])
        rwa [this] at hgc
      · have : ψB' g * ψB' g = ⟨y, hyN⟩ := Subtype.ext (by
          simp only [ψB', MonoidHom.codRestrict_apply, Subgroup.coe_mul, ← map_mul, h1, hr.zB])
        rw [← this]
        exact Subgroup.mul_mem _ hgc hgc
    have hle : N ≤ centralizer ({c * y} : Set H) := fun n hn =>
      (h.mem_cent_iff n).2 (by
        have := Subgroup.mem_center_iff.1 hyc ⟨n, hn⟩
        exact congrArg Subtype.val this)
    have hbot := h.perfect_free N hNperf hle
    exact (Subgroup.nontrivial_iff_ne_bot N).1 (CFSG.LocalCores.isQuasisimple_nontrivial hqs) hbot
  have hψz : ψ (QuaternionGroup.a 2) = π ⟨y, hyN⟩ := by
    show π (ψB' _) = _
    congr 1
    exact Subtype.ext (by simp [ψB', hr.zB])
  have hperfS : ∀ M : Subgroup (↥N ⧸ center ↥N), ⁅M, M⁆ = M →
      M ≤ centralizer ({ψ (QuaternionGroup.a 2)} : Set (↥N ⧸ center ↥N)) → M = ⊥ := by
    intro M hM hMc
    refine perfect_cent_descent (⟨y, hyN⟩ : ↥N) ?_ M hM ?_
    · intro M' hM' hM'c
      have hperf : ⁅M'.map N.subtype, M'.map N.subtype⁆ = M'.map N.subtype := by
        rw [← Subgroup.map_commutator, hM']
      have hle : M'.map N.subtype ≤ centralizer ({c * y} : Set H) := by
        rintro _ ⟨m, hm, rfl⟩
        rw [h.mem_cent_iff]
        have := Subgroup.mem_centralizer_singleton_iff.1 (hM'c hm)
        exact congrArg Subtype.val this
      have hbot := h.perfect_free _ hperf hle
      exact (Subgroup.map_eq_bot_iff_of_injective M' N.subtype_injective).1 hbot
    · intro m hm
      have := Subgroup.mem_centralizer_singleton_iff.1 (hMc hm)
      rw [hψz] at this
      exact this
  have hle : ∀ E : Subgroup (↥N ⧸ center ↥N), (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a * a = 1) → Nat.card E ≤ 4 := by
    intro E hEc hE2
    by_contra hcard
    push Not at hcard
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_two_of_sq E hE2)
    have hk3 : 3 ≤ k := by
      by_contra hk3
      push Not at hk3
      have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h8 : 8 ≤ Nat.card E := by
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
      omega
    exact not_gen4_of_elemAb_eight N ψA hcommA hZ E hEc hE2 h8 h.gen4
  have hPnonab : ∃ a b : ↥P, a * b ≠ b * a := nonab_of_simple_card (by rw [hP360]; norm_num)
  have hPcenter : center ↥P = ⊥ := center_eq_bot_of_simple_nonab hPnonab
  let φ : ↥P →* ↥N ⧸ center ↥N := π.comp (Subgroup.inclusion hPN)
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hpc : Subgroup.inclusion hPN p ∈ center ↥N := (QuotientGroup.eq_one_iff _).1 hp
    have : p ∈ center ↥P := by
      rw [Subgroup.mem_center_iff]
      intro q
      have := Subgroup.mem_center_iff.1 hpc (Subgroup.inclusion hPN q)
      exact Subtype.ext (congrArg (fun x : ↥N => (x : H)) this)
    rw [hPcenter] at this
    exact Subgroup.mem_bot.1 this
  let Pbar : Subgroup (↥N ⧸ center ↥N) := φ.range
  have hPbarcard : Nat.card Pbar = 360 := by
    rw [← hP360]
    exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  have hM11 := q3_S_cases hR hnonab hle ψ hψinj hperfS Pbar hPbarcard
  obtain ⟨e⟩ := hM11
  have hspor := CFSG.GH74.isSporadic_M11_of_mulEquiv_statedM11 e
  let α₀ : MulAut ↥N := MulAut.conjNormal u
  have hα₀ : ∀ n : ↥N, ((α₀ n : ↥N) : H) = u * (n : H) * u⁻¹ := fun n => rfl
  let α : MulAut (↥N ⧸ center ↥N) :=
    QuotientGroup.congr (center ↥N) (center ↥N) α₀ (Subgroup.map_center_eq α₀)
  have hα : ∀ n : ↥N, α (QuotientGroup.mk n) = QuotientGroup.mk (α₀ n) := fun n => rfl
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hα2 : α ^ 2 = 1 := by
    rw [pow_two]
    ext x
    induction x using QuotientGroup.induction_on with
    | H n =>
      show α (α (QuotientGroup.mk n)) = QuotientGroup.mk n
      rw [hα, hα]
      congr 1
      apply Subtype.ext
      rw [hα₀, hα₀]
      simp only [huinv]
      calc u * (u * (n : H) * u) * u = (u * u) * (n : H) * (u * u) := by group
        _ = n := by rw [hu]; group
  have hα1 : α = 1 := by
    by_contra hne
    have hsolv : Group.IsSolvable ↥Pbar := CFSG.GH74.KGroups.M11.fixed_solvable hspor α hα2 hne Pbar (by
      rintro _ ⟨p, rfl⟩
      show α (QuotientGroup.mk (Subgroup.inclusion hPN p)) = QuotientGroup.mk (Subgroup.inclusion hPN p)
      rw [hα]
      congr 1
      apply Subtype.ext
      rw [hα₀]
      have := Subgroup.mem_centralizer_singleton_iff.1 (hPu p.2)
      show u * (p : H) * u⁻¹ = p
      rw [← this]; group)
    have hsolvP : Group.IsSolvable ↥P :=
      Group.isSolvable_of_isSolvable_injective (f := φ.rangeRestrict) (fun a b hab => hφinj (congrArg Subtype.val hab))
    have := (IsSimpleGroup.comm_iff_isSolvable (G := ↥P)).2 hsolvP
    obtain ⟨a, b, hab⟩ := hPnonab
    exact hab (this a b)
  have hNperf' : ⁅(⊤ : Subgroup ↥N), (⊤ : Subgroup ↥N)⁆ = ⊤ := by
    have := Group.isPerfect_def.1 hqs.1
    rwa [_root_.commutator_def] at this
  have hA0 : α₀ = 1 := perfect_aut_eq_one hNperf' α₀ (fun g => by
    have := congrArg (fun a : MulAut (↥N ⧸ center ↥N) => a (QuotientGroup.mk g)) hα1
    simpa [hα] using this)
  have hNu : N ≤ centralizer ({u} : Set H) := by
    intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg (fun a : MulAut ↥N => ((a ⟨n, hn⟩ : ↥N) : H)) hA0
    simp only [hα₀] at this
    have h1 : u * n * u⁻¹ = n := this
    calc n * u = (u * n * u⁻¹) * u := by rw [h1]
      _ = u * n := by group
  have hNeP : N ≤ P := hmax N hNperf hNu
  have hNP : N = P := le_antisymm hNeP hPN
  subst hNP
  have hcen : center ↥N = ⊥ := hPcenter
  have hcardS : Nat.card (↥N ⧸ center ↥N) = 360 := by
    have hc1 : Nat.card ↥(center ↥N) = 1 := by rw [hcen]; exact Subgroup.card_bot
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥N)
    rw [hc1, mul_one, hP360] at this
    omega
  obtain ⟨e'⟩ := hspor
  have h7920 : Nat.card (↥N ⧸ center ↥N) = 7920 := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.GH74.KGroups.M11.card_M11
  omega

end CFSG.GH74.Generic.S1.Exo
