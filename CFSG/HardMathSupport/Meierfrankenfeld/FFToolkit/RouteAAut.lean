module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OuterBound

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.HardMathSupport.Cooperstein.Coordinator

variable {W : Type} [CommGroup W] [Finite W]

theorem psiAut_ne_one (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] (e : CQ L ≃* S) (hcent : Subgroup.center S = ⊥) {b : MulAut W}
    (hbE : b ∈ E) (hb1 : b ≠ 1) : psiAut L e (hE hbE) ≠ 1 := by
  intro h1
  have hb2 : b * b = 1 := by
    have := hEel.2 b hbE
    rwa [sq] at this
  have hbL : b ∈ L := mem_of_psiAut_inner hW hperf hirr hE hEel e hbE 1 (fun x => by
    rw [h1]; simp)
  have hs : e (QuotientGroup.mk ⟨b, hbL⟩) ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm x)
    have hx : x = e (QuotientGroup.mk y) := by rw [hy]; simp
    have h2 := psiAut_mk e (hE hbE) y
    rw [h1] at h2
    have h3 : conjAut L (hE hbE) y = ⟨b, hbL⟩ * y * ⟨b, hbL⟩⁻¹ :=
      Subtype.ext (coe_conjAut L (hE hbE) y)
    rw [MulAut.one_apply, h3, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      map_mul, map_mul, map_inv, ← hx] at h2
    have h4 : x = e (QuotientGroup.mk ⟨b, hbL⟩) * x * (e (QuotientGroup.mk ⟨b, hbL⟩))⁻¹ := h2
    calc x * e (QuotientGroup.mk ⟨b, hbL⟩)
        = (e (QuotientGroup.mk ⟨b, hbL⟩) * x * (e (QuotientGroup.mk ⟨b, hbL⟩))⁻¹) *
            e (QuotientGroup.mk ⟨b, hbL⟩) := by rw [← h4]
      _ = e (QuotientGroup.mk ⟨b, hbL⟩) * x := by group
  rw [hcent, Subgroup.mem_bot, ← map_one e] at hs
  have hmk : (QuotientGroup.mk (⟨b, hbL⟩ : ↥L) : CQ L) = 1 := e.injective hs
  rw [QuotientGroup.eq_one_iff] at hmk
  exact hb1 (eq_one_of_commutes_of_sq_eq_one hW hirr (fun l hl =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hmk ⟨l, hl⟩)) hb2)

theorem displacement_of_heisCfg_aut (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    {S : Type} [Group S] (e : CQ L ≃* S) {ρ p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    (hρ : 2 * ρ < (p - 1) * p ^ n * orderOf (2 : ZMod p) + 2)
    (hgen : ∀ ψ : MulAut S, ψ * ψ = 1 → ψ ≠ 1 → ∃ (x y : Fin (n + 1) → S) (z : S),
      HeisCfg p (n + 1) x y z ∧ (∀ i, y i ^ p = 1) ∧ ψ (x 0) = (x 0)⁻¹)
    {b : MulAut W} (hbN : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1)
    (hψ1 : psiAut L e hbN ≠ 1) : 2 ^ ρ ≤ (fixV (Subgroup.zpowers b)).index := by
  have hψ2 : psiAut L e hbN * psiAut L e hbN = 1 := by
    have hbb : b * b ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.normalizer (L : Set (MulAut W))).mul_mem hbN hbN
    rw [← psiAut_mul e hbN hbN hbb]
    have key : ∀ (c : MulAut W) (hc : c ∈ Subgroup.normalizer (L : Set (MulAut W))), c = 1 →
        psiAut L e hc = 1 := by
      rintro c hc rfl
      exact psiAut_one e hc
    exact key _ hbb hb2
  obtain ⟨x, y, z, h, hy, htx⟩ := hgen _ hψ2 hψ1
  let π : ↥L →* S := (e : CQ L →* S).comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hK : π.ker = Subgroup.center ↥L := by
    ext k
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk k) = 1 ↔ k ∈ Subgroup.center ↥L
    rw [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hKp : ¬ p ∣ Nat.card π.ker := by rw [hK]; exact hZ
  obtain ⟨x', y', z', h', hx'1, -, -, -⟩ := HeisCfg.exists_lift π hπ hK.le hKp h hy
  have hinv : conjAut L hbN (x' 0) = (x' 0)⁻¹ := by
    refine eq_of_map_eq_of_pow_eq_one π hK.le hKp
      (by rw [← map_pow, h'.xp 0, map_one]) (by rw [inv_pow, h'.xp 0, inv_one]) ?_
    have h1 : π (conjAut L hbN (x' 0)) = psiAut L e hbN (π (x' 0)) :=
      (psiAut_mk e hbN (x' 0)).symm
    rw [h1, hx'1, htx, map_inv, hx'1]
  have hz' : L.subtype z' ≠ 1 := fun hz1 => h'.z1 (L.subtype_injective (by rw [hz1, map_one]))
  have hinv' : b * L.subtype (x' 0) * b⁻¹ = (L.subtype (x' 0))⁻¹ := by
    have := congrArg Subtype.val hinv
    rw [coe_conjAut] at this
    simpa using this
  have h1 := two_pow_le_index_sq_of_heisCfg hW hp2 (h'.map L.subtype hz') hb2 hinv'
  exact two_pow_le_of_pow_le (index_fixV_eq_two_pow hW _) h1 hρ

theorem weight_lt_of_route_A_aut (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hq : CFSG.IsQuasisimple ↥L) (hirr : IsIrrOn L) {S : Type} [Group S] (e : CQ L ≃* S)
    (hcent : Subgroup.center S = ⊥)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    {m ρ p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hmρ : m < ρ)
    (hρ : 2 * ρ < (p - 1) * p ^ n * orderOf (2 : ZMod p) + 2)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    (hr : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ m)
    (hgen : ∀ ψ : MulAut S, ψ * ψ = 1 → ψ ≠ 1 → ∃ (x y : Fin (n + 1) → S) (z : S),
      HeisCfg p (n + 1) x y z ∧ (∀ i, y i ^ p = 1) ∧ ψ (x 0) = (x 0)⁻¹) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  apply weight_lt_of_lt_index
  have hperf : Group.IsPerfect ↥L := hq.1
  let Φ : ↥E →* MulAut S := psiHom L e hE
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    by_contra hb1
    exact psiAut_ne_one hW hperf hirr hE hEel e hcent b.2 (fun h => hb1 (Subtype.ext h)) hb
  have hBc : ∀ x ∈ Φ.range, ∀ y ∈ Φ.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEel.1 a a.2 b b.2)
  have hBs : ∀ x ∈ Φ.range, x * x = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by have := hEel.2 a a.2; simpa [pow_two] using this)
    rw [this, map_one]
  have hEcard : Nat.card E ≤ 2 ^ m := by
    have h1 : Nat.card E = Nat.card Φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [h1]
    exact hr _ hBc hBs
  obtain ⟨⟨b, hbE⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hb2 : b * b = 1 := by
    have := hEel.2 b hbE
    rwa [sq] at this
  have hdisp := displacement_of_heisCfg_aut hW e hp2 hZ hρ hgen (hE hbE) hb2
    (psiAut_ne_one hW hperf hirr hE hEel e hcent hbE hb1')
  have hmono : (fixV (Subgroup.zpowers b)).index ≤ (fixV E).index :=
    Subgroup.index_antitone (QuasithinUnique.Setup.X1.fixV_anti ((Subgroup.zpowers_le).2 hbE))
  calc Nat.card E ≤ 2 ^ m := hEcard
    _ < 2 ^ ρ := Nat.pow_lt_pow_right (by norm_num) hmρ
    _ ≤ (fixV (Subgroup.zpowers b)).index := hdisp
    _ ≤ (fixV E).index := hmono

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
