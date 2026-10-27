module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerLinear

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

variable {S : Type*} [CommGroup S]

theorem card_eq_twentyOne_of_oddTransitive_mulAut [Finite S] (hS : ∀ s : S, s ^ 2 = 1)
    {q n : ℕ} (hq : q = 2 ^ n) (hn : 2 ≤ n) {z : S} (hz : z ≠ 1) {W : Subgroup S}
    (hzW : IsCompl (Subgroup.zpowers z) W) (hW : Nat.card W = q) {Y : Subgroup (MulAut S)}
    (hYodd : Odd (Nat.card Y)) (hYtrans : ∀ v w : S, v ≠ 1 → w ≠ 1 → ∃ y ∈ Y, y v = w)
    {C₀ : Subgroup (MulAut S)} (hC₀Y : C₀ ≤ Y) (hC₀cyc : IsCyclic C₀)
    (hC₀card : Nat.card C₀ = q - 1) (hC₀z : ∀ c ∈ C₀, c z = z)
    (hC₀reg : ∀ w ∈ W, w ≠ 1 → ∀ w' ∈ W, w' ≠ 1 → ∃! c, c ∈ C₀ ∧ c w = w') :
    q = 4 ∧ Nat.card Y = 21 := by
  let : Module (ZMod 2) (Additive S) := AddCommGroup.zmodModule (n := 2) fun x => by
    change Additive.ofMul (x.toMul ^ 2) = 0
    rw [hS]
    rfl
  let ρ : MulAut S →* (Additive S ≃ₗ[ZMod 2] Additive S) :=
    { toFun := fun f => (MulEquiv.toAdditive f).toLinearEquiv (ZMod.map_smul _)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hρ : ∀ (f : MulAut S) (v : Additive S), ρ f v = Additive.ofMul (f v.toMul) :=
    fun _ _ => rfl
  have hρinj : Function.Injective ρ := by
    intro f g h
    ext s
    have := congrArg (fun φ : Additive S ≃ₗ[ZMod 2] Additive S => (φ (Additive.ofMul s)).toMul) h
    simpa [hρ] using this
  have hne : ∀ v : Additive S, v ≠ 0 ↔ v.toMul ≠ 1 := fun v => by
    rw [Ne, Ne, ← toMul_zero, Additive.toMul.injective.eq_iff]
  let W' : Submodule (ZMod 2) (Additive S) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup W)
  have hmemW' : ∀ v : Additive S, v ∈ W' ↔ v.toMul ∈ W := fun _ => Iff.rfl
  have hzW' : IsCompl (Submodule.span (ZMod 2) {Additive.ofMul z}) W' := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro v hv
      obtain ⟨hv₁, hv₂⟩ := Submodule.mem_inf.mp hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv₁
      have key : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
      rcases key a with rfl | rfl
      · rw [zero_smul]
        exact Submodule.zero_mem _
      · exfalso
        rw [one_smul, hmemW', toMul_ofMul] at hv₂
        have hz' : z ∈ Subgroup.zpowers z ⊓ W := ⟨Subgroup.mem_zpowers z, hv₂⟩
        rw [hzW.inf_eq_bot, Subgroup.mem_bot] at hz'
        exact hz hz'
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have hv : v.toMul ∈ Subgroup.zpowers z ⊔ W := by rw [hzW.sup_eq_top]; trivial
      obtain ⟨y, hy, w, hw, hyw⟩ := Subgroup.mem_sup.mp hv
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      refine Submodule.mem_sup.mpr ⟨Additive.ofMul (z ^ k), ?_, Additive.ofMul w, hw, ?_⟩
      · rw [ofMul_zpow]
        exact Submodule.mem_span_singleton.mpr ⟨(k : ZMod 2), by rw [Int.cast_smul_eq_zsmul]⟩
      · rw [← ofMul_mul, hyw, ofMul_toMul]
  have hW' : Nat.card W' = q := hW
  have hcardY : Nat.card (Y.map ρ) = Nat.card Y := Subgroup.card_map_of_injective hρinj
  rw [← hcardY]
  refine card_eq_twentyOne_of_oddTransitive hq hn (z := Additive.ofMul z)
    (by rw [hne, toMul_ofMul]; exact hz) hzW' hW' (hcardY ▸ hYodd) ?_ (Subgroup.map_mono hC₀Y)
    (isCyclic_of_surjective _ (ρ.subgroupMap_surjective C₀))
    ((Subgroup.card_map_of_injective hρinj).trans hC₀card) ?_ ?_
  · intro v w hv hw
    obtain ⟨y, hy, hyv⟩ := hYtrans v.toMul w.toMul ((hne v).mp hv) ((hne w).mp hw)
    exact ⟨ρ y, ⟨y, hy, rfl⟩, by rw [hρ, hyv, ofMul_toMul]⟩
  · rintro _ ⟨c, hc, rfl⟩
    rw [hρ, toMul_ofMul, hC₀z c hc]
  · intro w hw hw0 w' hw' hw'0
    obtain ⟨c, ⟨hc, hcw⟩, huniq⟩ :=
      hC₀reg w.toMul hw ((hne w).mp hw0) w'.toMul hw' ((hne w').mp hw'0)
    refine ⟨ρ c, ⟨⟨c, hc, rfl⟩, by rw [hρ, hcw, ofMul_toMul]⟩, ?_⟩
    rintro _ ⟨⟨d, hd, rfl⟩, hdw⟩
    rw [huniq d ⟨hd, by simpa [hρ] using congrArg Additive.toMul hdw⟩]

end CFSG.ProperTwoGeneratedCore.Assembly
