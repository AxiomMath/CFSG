module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Count
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Join
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Lift

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance.Alt

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type*} [Group G] [Finite G]

theorem barX_gLBConj (p : ℕ) {X : Subgroup G} {g : G} (hg : g ∈ X) (K : Subgroup G) :
    barX p X (GLBConj g K) =
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hg⟩) (barX p X K) := by
  ext y
  rw [mem_gLBConj]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, (Subgroup.mem_subgroupOf).2 ?_, by simp [map_mul]⟩
    have := mem_gLBConj.1 ((Subgroup.mem_subgroupOf).1 hx)
    simpa using this
  · rintro ⟨w, hw, hwy⟩
    have hw' : (w : G) ∈ K := (Subgroup.mem_subgroupOf).1 hw
    refine ⟨⟨g, hg⟩⁻¹ * w * ⟨g, hg⟩, (Subgroup.mem_subgroupOf).2 ?_, ?_⟩
    · rw [mem_gLBConj]
      show g * (g⁻¹ * (w : G) * g) * g⁻¹ ∈ K
      have e : g * (g⁻¹ * (w : G) * g) * g⁻¹ = w := by group
      rw [e]
      exact hw'
    · rw [map_mul, map_mul, map_inv]
      have : QuotientGroup.mk' (GLAPPrimeCore p ↥X) w =
          QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hg⟩ * y *
            (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hg⟩)⁻¹ := hwy
      rw [this]
      group

theorem gLBConj_eq_iff_mem_normalizer (L : Subgroup G) (a b : G) :
    GLBConj a L = GLBConj b L ↔ b * a⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  constructor
  · intro h
    have h1 := congrArg (GLBConj a⁻¹) h
    rw [gLBConj_inv_gLBConj, gLBConj_gLBConj] at h1
    exact h1.symm
  · intro h
    have h1 : GLBConj a⁻¹ (GLBConj b L) = L := by rw [gLBConj_gLBConj]; exact h
    have h2 := congrArg (GLBConj a) h1
    rw [gLBConj_gLBConj_inv] at h2
    exact h2.symm

theorem centB_comm_theta {p : ℕ} {X L B : Subgroup G} (hL : GLAPComponent p X L) {c : G}
    (hc : c ∈ centB p B L) (hcX : c ∈ X) (ℓ : ↥L) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨c, hcX⟩ *
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) (Subgroup.inclusion hL.1 ℓ) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) (Subgroup.inclusion hL.1 ℓ) *
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨c, hcX⟩ := by
  obtain ⟨hb, hcB, h1⟩ := mem_centB.1 hc
  have h2 := congrArg (fun a => a (QuotientGroup.mk ℓ)) h1
  simp only [MulAut.one_apply] at h2
  rw [barAut_mk] at h2
  have h3 := congrArg (barTheta p hL.1 hL.2.1) h2
  rw [barTheta_mk, barTheta_mk] at h3
  have key : Subgroup.inclusion hL.1 ((Subgroup.normalizerMonoidHom L) ⟨c, hb⟩ ℓ) =
      ⟨c, hcX⟩ * Subgroup.inclusion hL.1 ℓ * ⟨c, hcX⟩⁻¹ := by
    apply Subtype.ext
    simp
  rw [key] at h3
  change QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨c, hcX⟩ * Subgroup.inclusion hL.1 ℓ *
    ⟨c, hcX⟩⁻¹) = _ at h3
  rw [map_mul, map_mul, map_inv] at h3
  calc _ = (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨c, hcX⟩ *
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) (Subgroup.inclusion hL.1 ℓ) *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨c, hcX⟩)⁻¹) *
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨c, hcX⟩ := by group
    _ = _ := by rw [h3]; rfl

@[expose] noncomputable def c0Hom (p : ℕ) {X : Subgroup G} (B L : Subgroup G) (hBX : B ≤ X) :
    ↥(centB p B L) →* ↥X ⧸ GLAPPrimeCore p ↥X :=
  (QuotientGroup.mk' (GLAPPrimeCore p ↥X)).comp (Subgroup.inclusion ((centB_le p B L).trans hBX))

theorem c0Hom_injective {p : ℕ} {X B : Subgroup G} (L : Subgroup G) (hBX : B ≤ X)
    (hB : IsElemAbelian p B) : Function.Injective (c0Hom p B L hBX) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have h1 : Subgroup.inclusion ((centB_le p B L).trans hBX) c ∈ GLAPPrimeCore p ↥X :=
    (QuotientGroup.eq_one_iff _).1 hc
  set u : ↥(GLAPPrimeCore p ↥X) := ⟨_, h1⟩ with hu
  have hcB : ((c : ↥(centB p B L)) : G) ∈ B := centB_le p B L c.2
  have hup : u ^ p = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [hu] using hB.2 _ hcB
  have h2 : orderOf u ∣ p := orderOf_dvd_of_pow_eq_one hup
  have h3 : orderOf u ∣ Nat.card (GLAPPrimeCore p ↥X) := orderOf_dvd_natCard u
  have hcop := coprime_card_gLAPPrimeCore_aux p ↥X
  have h4 : orderOf u = 1 := by
    have := Nat.dvd_gcd h2 h3
    rw [hcop] at this
    exact Nat.dvd_one.1 this
  have h5 : u = 1 := orderOf_eq_one_iff.1 h4
  have h6 := congrArg (fun w : ↥(GLAPPrimeCore p ↥X) => ((w : ↥X) : G)) h5
  apply Subtype.ext
  simpa [hu] using h6

theorem exists_twoLocal_lower {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X B L : Subgroup G}
    (hBX : B ≤ X) (hB : IsElemAbelian p B) (hL : GLAPComponent p X L)
    (hZ : ∀ x : barOf p L, (∀ y, x * y = y * x) → x = 1)
    (E' T' : Subgroup (barOf p L)) (q : ℕ)
    (hE' : IsMulCommutative E' ∧ (∀ x ∈ E', x ^ p = 1) ∧ Nat.card E' = p ^ q)
    (hT' : T' ≠ ⊥ ∧ IsPGroup 2 T') (hET : E' ≤ Subgroup.centralizer (T' : Set (barOf p L))) :
    ∃ P S : Subgroup ↥X, IsMulCommutative P ∧ (∀ x ∈ P, x ^ p = 1) ∧
      Nat.card P = Nat.card (centB p B L) *
        p ^ (q * (B ⊓ Subgroup.normalizer (L : Set G)).relIndex B) ∧
      S ≠ ⊥ ∧ IsPGroup 2 S ∧ P ≤ Subgroup.normalizer (S : Set ↥X) := by
  classical
  set π : ↥X →* ↥X ⧸ GLAPPrimeCore p ↥X := QuotientGroup.mk' _ with hπ
  set θ := barTheta p hL.1 hL.2.1 with hθ
  have hθinj := barTheta_injective p hL.1 hL.2.1
  let πB : ↥B →* ↥X ⧸ GLAPPrimeCore p ↥X := π.comp (Subgroup.inclusion hBX)
  have hBc : IsMulCommutative B := hB.1
  let I := ↥B ⧸ ((B ⊓ Subgroup.normalizer (L : Set G)).subgroupOf B)
  have : Fintype I := Fintype.ofFinite I
  obtain ⟨r, hr⟩ : ∃ r : I → ↥B, ∀ i, (QuotientGroup.mk (r i) : I) = i :=
    ⟨fun i => (QuotientGroup.mk_surjective i).choose,
      fun i => (QuotientGroup.mk_surjective i).choose_spec⟩
  let ψ : I → (barOf p L →* ↥X ⧸ GLAPPrimeCore p ↥X) :=
    fun i => (MulAut.conj (πB (r i))⁻¹).toMonoidHom.comp θ
  have hψ : ∀ i, Function.Injective (ψ i) := fun i =>
    (MulAut.conj (πB (r i))⁻¹).injective.comp hθinj
  let Y : I → Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := fun i => (ψ i).range
  let E : I → Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := fun i => E'.map (ψ i)
  have hYbar : ∀ i, Y i = barX p X (GLBConj ((r i : ↥B) : G) L) := by
    intro i
    rw [barX_gLBConj p (hBX (r i).2) L, ← barTheta_range p hL.1 hL.2.1]
    exact MonoidHom.range_comp _ _
  have hcomp : ∀ i, GLAPComponent p X (GLBConj ((r i : ↥B) : G) L) := by
    intro i
    have h := glaPComponent_gLBConj hL ((r i : ↥B) : G)
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (hBX (r i).2))] at h
  have hYcomm : ∀ i j, i ≠ j → Y i ≤ Subgroup.centralizer (Y j : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    intro i j hij
    have hne : barX p X (GLBConj ((r i : ↥B) : G) L) ≠ barX p X (GLBConj ((r j : ↥B) : G) L) := by
      intro h
      have h1 := glaPComponent_uniqueAux (hcomp i) (hcomp j) h
      have h2 := (gLBConj_eq_iff_mem_normalizer L _ _).1 h1
      apply hij
      rw [← hr i, ← hr j]
      apply QuotientGroup.eq.2
      rw [Subgroup.mem_subgroupOf]
      have h3 : (((r i)⁻¹ * r j : ↥B)) = r j * (r i)⁻¹ := hBc.is_comm.comm _ _
      rw [h3]
      exact ⟨((r j * (r i)⁻¹ : ↥B)).2, h2⟩
    have this : ⁅barX p X (GLBConj ((r i : ↥B) : G) L), barX p X (GLBConj ((r j : ↥B) : G) L)⁆ =
        ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hcomp i).2.2.1
        (hcomp j).2.2.1 hne
    rw [← hYbar i, ← hYbar j] at this
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 this
  have hEY : ∀ i, E i ≤ Y i := fun i => Subgroup.map_le_range (ψ i) E'
  have hYz : ∀ i, ∀ y ∈ Y i, (∀ y' ∈ Y i, y * y' = y' * y) → y = 1 := by
    intro i y hy hc
    obtain ⟨x, rfl⟩ := hy
    have : x = 1 := hZ x fun z => hψ i (by
      rw [map_mul, map_mul]
      exact hc (ψ i z) ⟨z, rfl⟩)
    rw [this, map_one]
  let C0 : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := (c0Hom p B L hBX).range
  have hC0Y : ∀ i, C0 ≤ Subgroup.centralizer (Y i : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    intro i
    rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, rfl⟩
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective z
    have hcX : ((c : ↥(centB p B L)) : G) ∈ X := hBX (centB_le p B L c.2)
    have h1 := centB_comm_theta (X := X) hL c.2 hcX ℓ
    have h2 : Commute (c0Hom p B L hBX c) (πB (r i)) := by
      show π _ * π _ = π _ * π _
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (c : G) * ((r i : ↥B) : G) = ((r i : ↥B) : G) * (c : G)
      exact congrArg Subtype.val (hBc.is_comm.comm (⟨(c : G), centB_le p B L c.2⟩ : ↥B) (r i))
    have h3 : Commute (c0Hom p B L hBX c) (θ (QuotientGroup.mk ℓ)) := h1
    have h4 : Commute (c0Hom p B L hBX c) (ψ i (QuotientGroup.mk ℓ)) := by
      show Commute _ ((πB (r i))⁻¹ * θ (QuotientGroup.mk ℓ) * (πB (r i))⁻¹⁻¹)
      exact (h2.inv_right.mul_right h3).mul_right h2.inv_right.inv_right
    exact h4.symm.eq
  have hCc : IsMulCommutative ↥(centB p B L) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have := hBc.is_comm.comm (⟨(a : G), centB_le p B L a.2⟩ : ↥B)
      ⟨(b : G), centB_le p B L b.2⟩
    have h2 : (a : G) * (b : G) = (b : G) * (a : G) := by
      have := congrArg Subtype.val this
      simpa using this
    exact Subtype.ext h2
  have hC : IsMulCommutative C0 ∧ ∀ x ∈ C0, x ^ p = 1 := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      show (a : ↥X ⧸ GLAPPrimeCore p ↥X) * b = b * a
      rw [← hx, ← hy, ← map_mul, ← map_mul, hCc.is_comm.comm x y]
    · rintro _ ⟨c, rfl⟩
      rw [← map_pow]
      have : c ^ p = 1 := Subtype.ext (hB.2 _ (centB_le p B L c.2))
      rw [this, map_one]
  have hCcard : Nat.card C0 = Nat.card (centB p B L) :=
    (Nat.card_congr (MonoidHom.ofInjective (c0Hom_injective L hBX hB)).toEquiv).symm
  have hE : ∀ i, IsMulCommutative (E i) ∧ (∀ x ∈ E i, x ^ p = 1) ∧ Nat.card (E i) = p ^ q := by
    intro i
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyb⟩ := b.2
      apply Subtype.ext
      show (a : ↥X ⧸ GLAPPrimeCore p ↥X) * b = b * a
      rw [← hxa, ← hyb, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hE'.1.is_comm.comm (⟨x, hx⟩ : E') ⟨y, hy⟩)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE'.2.1 x hx, map_one]
    · rw [Subgroup.card_map_of_injective (hψ i)]
      exact hE'.2.2
  obtain ⟨Pbar, hPc, hPe, hPcard, hPT⟩ := exists_elemAbelian_join hp Y E C0 q hYcomm hEY hYz hC0Y hC hE
  have hI : Nonempty I := ⟨1⟩
  obtain ⟨i0⟩ := hI
  let Tbar : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := T'.map (ψ i0)
  have hTY : Tbar ≤ Y i0 := Subgroup.map_le_range (ψ i0) T'
  have hTbar : Tbar ≠ ⊥ := fun h => hT'.1 ((Subgroup.map_eq_bot_iff_of_injective T' (hψ i0)).1 h)
  have hTbar2 : IsPGroup 2 Tbar := hT'.2.map (ψ i0)
  have hCT : C0 ≤ Subgroup.centralizer (Tbar : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := fun x hx =>
    Subgroup.centralizer_le hTY (hC0Y i0 hx)
  have hET' : ∀ i, E i ≤ Subgroup.centralizer (Tbar : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    intro i
    by_cases hi : i = i0
    · subst hi
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨t, ht, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 (hET hx) t ht
      rw [← map_mul, ← map_mul, this]
    · exact (Subgroup.centralizer_le hTY).trans' (hEY i |>.trans (hYcomm i i0 hi))
  have hPcent := hPT Tbar hCT hET'
  obtain ⟨P, S, hPc', hPe', hPcard', hS, hS2, hPS⟩ := exists_lift_twoLocal hp hp2
    (GLAPPrimeCore p ↥X) (coprime_card_gLAPPrimeCore_aux p ↥X) Pbar Tbar ⟨hPc, hPe⟩
    ⟨hTbar, hTbar2⟩ hPcent
  refine ⟨P, S, hPc', hPe', ?_, hS, hS2, hPS⟩
  have hidx : Fintype.card I = (B ⊓ Subgroup.normalizer (L : Set G)).relIndex B := by
    rw [← Nat.card_eq_fintype_card, Subgroup.relIndex, Subgroup.index_eq_card]
  rw [hPcard', hPcard, hCcard, hidx]

end CFSG.HardMathSupport.Timmesfeld.Balance.Alt
