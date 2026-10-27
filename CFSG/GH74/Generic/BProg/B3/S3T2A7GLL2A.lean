module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7WS

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7.GLR

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

variable {Y : Type} [Group Y] [Finite Y] {L B X₀ : Subgroup Y} {z : Y}

theorem odd_card_W (X₀ : Subgroup Y) : Odd (Nat.card ↥(pPrimeCoreOf 2 X₀)) := by
  rw [pPrimeCoreOf, Subgroup.card_map_of_injective X₀.subtype_injective]
  exact TwoThin.odd_card_pPrimeCore _

theorem centralizer_le_normalizer_W (hs : Setting125 Y L B X₀ z) {D : Subgroup Y} (hDB : D ≤ B)
    (hDz : D ⊓ zpowers z = ⊥) (hDsup : D ⊔ zpowers z = B) {E : Subgroup Y} (hED : E ≤ D)
    (hE : 2 ≤ pRank 2 ↥E) :
    centralizer (E : Set Y) ≤ normalizer (pPrimeCoreOf 2 X₀ : Set Y) := by
  intro g hg
  obtain ⟨-, hEr⟩ := compl_facts hs hDB hDz hDsup
  have hE' : 3 ≤ pRank 2 ↥(E ⊔ zpowers z) := hEr E hED hE
  have hE'B : E ⊔ zpowers z ≤ B := sup_le (hED.trans hDB) (zpowers_le.mpr hs.z_mem)
  have hle : E ⊔ zpowers z ≤ centralizer ({g} : Set Y) := by
    refine sup_le (fun e he => mem_centralizer_singleton_iff.mpr ?_) (zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_iff.mp hg e he
    · exact mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hs.z_cent g).symm
  have hgc : g ∈ centralizer ((E ⊔ zpowers z : Subgroup Y) : Set Y) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hle hh)
  have hNE : normalizer ((E ⊔ zpowers z : Subgroup Y) : Set Y) ≤ gammaK 2 B 3 :=
    le_iSup₂_of_le (E ⊔ zpowers z) hE'B (le_iSup_of_le hE' le_rfl)
  have hXW : X₀ ≤ normalizer (pPrimeCoreOf 2 X₀ : Set Y) := fun x hx =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hx)
  exact hXW (hs.gamma (hNE (Subgroup.centralizer_le_normalizer _ hgc)))

omit [Finite Y] in
theorem mem_centralizer_of_comm_mem_centerL {L : Subgroup Y} (hperf : Group.IsPerfect ↥L)
    {w : Y} (hwN : w ∈ normalizer (L : Set Y))
    (h : ∀ c ∈ L, ∀ y ∈ L, w * c * w⁻¹ * c⁻¹ * y = y * (w * c * w⁻¹ * c⁻¹)) :
    w ∈ centralizer (L : Set Y) := by
  have hmem : ∀ c : ↥L, w * c * w⁻¹ * (c : Y)⁻¹ ∈ L := fun c =>
    mul_mem ((mem_normalizer_iff.mp hwN c).mp c.2) (inv_mem c.2)
  have hcen : ∀ c : ↥L, (⟨w * c * w⁻¹ * (c : Y)⁻¹, hmem c⟩ : ↥L) ∈ center ↥L := fun c =>
    mem_center_iff.mpr fun y => Subtype.ext (h c c.2 y y.2).symm
  let f : ↥L →* ↥(center ↥L) :=
    { toFun := fun c => ⟨⟨w * c * w⁻¹ * (c : Y)⁻¹, hmem c⟩, hcen c⟩
      map_one' := by ext; simp
      map_mul' := fun c₁ c₂ => by
        apply Subtype.ext
        apply Subtype.ext
        change w * ((c₁ : Y) * c₂) * w⁻¹ * ((c₁ : Y) * c₂)⁻¹ =
          (w * c₁ * w⁻¹ * (c₁ : Y)⁻¹) * (w * c₂ * w⁻¹ * (c₂ : Y)⁻¹)
        have h2 := h c₂ c₂.2 _ (inv_mem c₁.2)
        calc w * ((c₁ : Y) * c₂) * w⁻¹ * ((c₁ : Y) * c₂)⁻¹
            = w * c₁ * w⁻¹ * ((w * c₂ * w⁻¹ * (c₂ : Y)⁻¹) * (c₁ : Y)⁻¹) := by group
          _ = w * c₁ * w⁻¹ * ((c₁ : Y)⁻¹ * (w * c₂ * w⁻¹ * (c₂ : Y)⁻¹)) := by rw [h2]
          _ = (w * c₁ * w⁻¹ * (c₁ : Y)⁻¹) * (w * c₂ * w⁻¹ * (c₂ : Y)⁻¹) := by group }
  have hker : commutator ↥L ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [hperf.commutator_eq_top] at hker
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have h1 : f ⟨c, hc⟩ = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top _))
  have h2 : w * c * w⁻¹ * c⁻¹ = 1 := congrArg (fun u : ↥(center ↥L) => ((u : ↥L) : Y)) h1
  calc c * w = (w * c * w⁻¹ * c⁻¹)⁻¹ * (w * c) := by group
    _ = w * c := by rw [h2, inv_one, one_mul]

theorem false_of_sig_of_inner (hs : Setting125 Y L B X₀ z) (hsig : Sig125 L X₀)
    (hgen : ∀ c ∈ L, ∃ x ∈ normalizer (pPrimeCoreOf 2 X₀ : Set Y),
      x ∈ normalizer (L : Set Y) ∧ ∀ y ∈ L, x * y * x⁻¹ = c * y * c⁻¹) : False := by
  classical
  set W : Subgroup Y := pPrimeCoreOf 2 X₀ with hW
  obtain ⟨w, hwW, hwN, hwC⟩ := hsig
  have hWodd : Odd (Nat.card ↥W) := odd_card_W X₀
  have hxi : ∀ x c : Y, (∀ y ∈ L, x * y * x⁻¹ = c * y * c⁻¹) → c ∈ L → ∀ y ∈ L,
      x⁻¹ * y * x = c⁻¹ * y * c := by
    intro x c hx hc y hy
    have h := hx _ (mul_mem (mul_mem (inv_mem hc) hy) hc)
    calc x⁻¹ * y * x = x⁻¹ * (c * (c⁻¹ * y * c) * c⁻¹) * x := by group
      _ = x⁻¹ * (x * (c⁻¹ * y * c) * x⁻¹) * x := by rw [h]
      _ = c⁻¹ * y * c := by group
  let P : ↥L → Prop := fun l =>
    ∃ u ∈ W, u ∈ normalizer (L : Set Y) ∧ ∀ y ∈ L, u * y * u⁻¹ = l * y * (l : Y)⁻¹
  have hPmul : ∀ a b, P a → P b → P (a * b) := by
    rintro a b ⟨u, huW, huN, hu⟩ ⟨v, hvW, hvN, hv⟩
    refine ⟨u * v, mul_mem huW hvW, mul_mem huN hvN, fun y hy => ?_⟩
    calc u * v * y * (u * v)⁻¹ = u * (v * y * v⁻¹) * u⁻¹ := by group
      _ = u * ((b : Y) * y * (b : Y)⁻¹) * u⁻¹ := by rw [hv y hy]
      _ = (a : Y) * ((b : Y) * y * (b : Y)⁻¹) * (a : Y)⁻¹ :=
          hu _ (mul_mem (mul_mem b.2 hy) (inv_mem b.2))
      _ = ((a * b : ↥L) : Y) * y * ((a * b : ↥L) : Y)⁻¹ := by
          simp only [Subgroup.coe_mul]
          group
  have hPinv : ∀ a, P a → P a⁻¹ := by
    rintro a ⟨u, huW, huN, hu⟩
    refine ⟨u⁻¹, inv_mem huW, inv_mem huN, fun y hy => ?_⟩
    rw [inv_inv, hxi u a hu a.2 y hy]
    simp only [Subgroup.coe_inv, inv_inv]
  let N' : Subgroup ↥L :=
    { carrier := {l | P l}
      mul_mem' := fun {a b} ha hb => hPmul a b ha hb
      one_mem' := ⟨1, one_mem _, one_mem _, fun y _ => by simp⟩
      inv_mem' := fun {a} ha => hPinv a ha }
  have hN'n : N'.Normal := by
    refine ⟨fun l hl c => ?_⟩
    obtain ⟨u, huW, huN, hu⟩ := hl
    obtain ⟨x, hxW, hxL, hx⟩ := hgen c c.2
    refine ⟨x * u * x⁻¹, (mem_normalizer_iff.mp hxW u).mp huW,
      mul_mem (mul_mem hxL huN) (inv_mem hxL), fun y hy => ?_⟩
    have h1 : (c : Y)⁻¹ * y * c ∈ L := mul_mem (mul_mem (inv_mem c.2) hy) c.2
    have h2 : (l : Y) * ((c : Y)⁻¹ * y * c) * (l : Y)⁻¹ ∈ L :=
      mul_mem (mul_mem l.2 h1) (inv_mem l.2)
    calc x * u * x⁻¹ * y * (x * u * x⁻¹)⁻¹ = x * (u * (x⁻¹ * y * x) * u⁻¹) * x⁻¹ := by group
      _ = x * (u * ((c : Y)⁻¹ * y * c) * u⁻¹) * x⁻¹ := by rw [hxi x c hx c.2 y hy]
      _ = x * ((l : Y) * ((c : Y)⁻¹ * y * c) * (l : Y)⁻¹) * x⁻¹ := by rw [hu _ h1]
      _ = (c : Y) * ((l : Y) * ((c : Y)⁻¹ * y * c) * (l : Y)⁻¹) * (c : Y)⁻¹ := hx _ h2
      _ = ((c * l * c⁻¹ : ↥L) : Y) * y * ((c * l * c⁻¹ : ↥L) : Y)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hs.comp.1 hN'n with htop | hcen
  ·
    obtain ⟨-, hsimp, hnab⟩ := hs.comp.1
    obtain ⟨t, ht⟩ := (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab).2
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective t
    have hl : l ∈ N' := htop ▸ Subgroup.mem_top l
    obtain ⟨u, huW, -, hu⟩ := hl
    have hpow : ∀ k : ℕ, ∀ y ∈ L, u ^ k * y * (u ^ k)⁻¹ = (l : Y) ^ k * y * ((l : Y) ^ k)⁻¹ := by
      intro k
      induction k with
      | zero => intro y _; simp
      | succ k ih =>
        intro y hy
        have h1 : (l : Y) * y * (l : Y)⁻¹ ∈ L := mul_mem (mul_mem l.2 hy) (inv_mem l.2)
        calc u ^ (k + 1) * y * (u ^ (k + 1))⁻¹ = u ^ k * (u * y * u⁻¹) * (u ^ k)⁻¹ := by group
          _ = u ^ k * ((l : Y) * y * (l : Y)⁻¹) * (u ^ k)⁻¹ := by rw [hu y hy]
          _ = (l : Y) ^ k * ((l : Y) * y * (l : Y)⁻¹) * ((l : Y) ^ k)⁻¹ := ih _ h1
          _ = (l : Y) ^ (k + 1) * y * ((l : Y) ^ (k + 1))⁻¹ := by group
    have hum : u ^ Nat.card ↥W = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (x := (⟨u, huW⟩ : ↥W)))
    have hlm : l ^ Nat.card ↥W ∈ center ↥L := by
      refine mem_center_iff.mpr fun g => Subtype.ext ?_
      have h1 := hpow (Nat.card ↥W) g g.2
      rw [hum, one_mul, inv_one, mul_one] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      set m := Nat.card ↥W
      calc (g : Y) * (l : Y) ^ m = ((l : Y) ^ m * g * ((l : Y) ^ m)⁻¹) * (l : Y) ^ m := by
            rw [← h1]
        _ = (l : Y) ^ m * g := by group
    have h1 : (QuotientGroup.mk l : ↥L ⧸ center ↥L) ^ Nat.card ↥W = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hlm
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [ht] at h2
    exact (Nat.not_even_iff_odd.mpr hWodd) (even_iff_two_dvd.mpr h2)
  ·
    apply hwC
    refine mem_centralizer_of_comm_mem_centerL hs.comp.1.1 hwN fun c hc y hy => ?_
    obtain ⟨x, hxW, hxL, hx⟩ := hgen c hc
    have hcL : w * c * w⁻¹ * c⁻¹ ∈ L :=
      mul_mem ((mem_normalizer_iff.mp hwN c).mp hc) (inv_mem hc)
    have hmem : (⟨w * c * w⁻¹ * c⁻¹, hcL⟩ : ↥L) ∈ N' := by
      refine ⟨w * (x * w⁻¹ * x⁻¹), mul_mem hwW ((mem_normalizer_iff.mp hxW _).mp (inv_mem hwW)),
        mul_mem hwN (mul_mem (mul_mem hxL (inv_mem hwN)) (inv_mem hxL)), fun y' hy' => ?_⟩
      have h1 : c⁻¹ * y' * c ∈ L := mul_mem (mul_mem (inv_mem hc) hy') hc
      have h2 : w⁻¹ * (c⁻¹ * y' * c) * w ∈ L := by
        have := (mem_normalizer_iff.mp (inv_mem hwN) _).mp h1
        rwa [inv_inv] at this
      calc w * (x * w⁻¹ * x⁻¹) * y' * (w * (x * w⁻¹ * x⁻¹))⁻¹ =
            w * (x * (w⁻¹ * (x⁻¹ * y' * x) * w) * x⁻¹) * w⁻¹ := by group
        _ = w * (x * (w⁻¹ * (c⁻¹ * y' * c) * w) * x⁻¹) * w⁻¹ := by rw [hxi x c hx hc y' hy']
        _ = w * (c * (w⁻¹ * (c⁻¹ * y' * c) * w) * c⁻¹) * w⁻¹ := by rw [hx _ h2]
        _ = (w * c * w⁻¹ * c⁻¹) * y' * (w * c * w⁻¹ * c⁻¹)⁻¹ := by group
    have h3 := congrArg Subtype.val (mem_center_iff.mp (hcen hmem) ⟨y, hy⟩)
    exact h3.symm

end CFSG.GH74.Generic.BProg.B3.S3T2A7.GLR
