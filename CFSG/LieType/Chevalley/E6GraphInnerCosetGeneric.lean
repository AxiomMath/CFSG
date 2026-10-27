module

public import CFSG.LieType.Chevalley.E6GraphLeviIntersections
public import CFSG.LieType.Chevalley.E6GraphRootSL2Basic

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphInnerCoset

section Generic

variable {M : Type*} [Group M]

theorem isPGroup_iff_forall_mem {p : ℕ} {H : Subgroup M} :
    IsPGroup p ↥H ↔ ∀ h ∈ H, ∃ n : ℕ, h ^ p ^ n = 1 := by
  constructor
  · intro hH h hh
    obtain ⟨n, hn⟩ := hH ⟨h, hh⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  · intro hH h
    obtain ⟨n, hn⟩ := hH h h.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

theorem inv_pow_mul_pow_mem {Q : Subgroup M} {x q : M}
    (hx : x ∈ Subgroup.normalizer (Q : Set M)) (hq : q ∈ Q) (m : ℕ) :
    (x ^ m)⁻¹ * (x * q) ^ m ∈ Q := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : x⁻¹ * ((x ^ m)⁻¹ * (x * q) ^ m) * x ∈ Q :=
      (Subgroup.mem_normalizer_iff''.1 hx _).1 ih
    have e : (x ^ (m + 1))⁻¹ * (x * q) ^ (m + 1) =
        (x⁻¹ * ((x ^ m)⁻¹ * (x * q) ^ m) * x) * q := by
      rw [pow_succ, pow_succ, mul_inv_rev]
      group
    rw [e]
    exact mul_mem h1 hq

theorem isPGroup_sup_of_isPGroup_sup_conj {p : ℕ} {Q L A B : Subgroup M} (hQL : Q ⊓ L = ⊥)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set M)) (hA : A ≤ L) (hB : B ≤ L) {q : M}
    (hq : q ∈ Q) (h : IsPGroup p ↥(A ⊔ B.map (MulAut.conj q).toMonoidHom)) :
    IsPGroup p ↥(A ⊔ B) := by
  have hQN : Q ≤ Subgroup.normalizer (Q : Set M) := Subgroup.le_normalizer
  let S : Subgroup M :=
    { carrier := {y | y ∈ L ∧ ∃ y₁ ∈ A ⊔ B.map (MulAut.conj q).toMonoidHom, y₁⁻¹ * y ∈ Q}
      mul_mem' := by
        rintro y z ⟨hy, y₁, hy₁, hyq⟩ ⟨hz, z₁, hz₁, hzq⟩
        refine ⟨mul_mem hy hz, y₁ * z₁, mul_mem hy₁ hz₁, ?_⟩
        have e : (y₁ * z₁)⁻¹ * (y * z) = z₁⁻¹ * z * (z⁻¹ * (y₁⁻¹ * y) * z) := by group
        rw [e]
        exact mul_mem hzq ((Subgroup.mem_normalizer_iff''.1 (hLQ hz) _).1 hyq)
      one_mem' := ⟨one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro y ⟨hy, y₁, hy₁, hyq⟩
        refine ⟨inv_mem hy, y₁⁻¹, inv_mem hy₁, ?_⟩
        have e : y₁⁻¹⁻¹ * y⁻¹ = y * (y₁⁻¹ * y)⁻¹ * y⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.1 (hLQ hy) _).1 (inv_mem hyq) }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨hA ha, a, Subgroup.mem_sup_left ha, by simp⟩)
    fun b hb => ⟨hB hb, q * b * q⁻¹, Subgroup.mem_sup_right ⟨b, hb, rfl⟩, by
      have e : (q * b * q⁻¹)⁻¹ * b = q * (b⁻¹ * q⁻¹ * b) := by group
      rw [e]
      exact mul_mem hq ((Subgroup.mem_normalizer_iff''.1 (hLQ (hB hb)) _).1 (inv_mem hq))⟩
  rw [isPGroup_iff_forall_mem] at h ⊢
  intro x hx
  obtain ⟨hxL, x₁, hx₁, hxq⟩ := hle hx
  obtain ⟨n, hn⟩ := h x₁ hx₁
  have hx₁N : x₁ ∈ Subgroup.normalizer (Q : Set M) := by
    have : A ⊔ B.map (MulAut.conj q).toMonoidHom ≤ Subgroup.normalizer (Q : Set M) := by
      refine sup_le (hA.trans hLQ) ?_
      rintro _ ⟨b, hb, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem (hQN hq) (hLQ (hB hb))) (inv_mem (hQN hq))
    exact this hx₁
  refine ⟨n, ?_⟩
  have h1 := inv_pow_mul_pow_mem hx₁N hxq (p ^ n)
  rw [hn, inv_one, one_mul, show x₁ * (x₁⁻¹ * x) = x by group] at h1
  have h2 : x ^ p ^ n ∈ Q ⊓ L := Subgroup.mem_inf.2 ⟨h1, pow_mem hxL _⟩
  rwa [hQL, Subgroup.mem_bot] at h2

theorem levi_sq_eq_one {Q L : Subgroup M} (hQL : Q ⊓ L = ⊥)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set M)) {P : M} (hPP : P * P = 1)
    (hPQ : ∀ q ∈ Q, P * q * P⁻¹ ∈ Q) (hPL : ∀ l ∈ L, P * l * P⁻¹ ∈ L) {q l : M} (hq : q ∈ Q)
    (hl : l ∈ L) (h : (q * l * P) ^ 2 = 1) : (l * P) ^ 2 = 1 := by
  have hPinv : P⁻¹ = P := (eq_inv_of_mul_eq_one_left hPP).symm
  have hq' : q * (l * (P * q * P⁻¹) * l⁻¹) ∈ Q :=
    mul_mem hq ((Subgroup.mem_normalizer_iff.1 (hLQ hl) _).1 (hPQ q hq))
  have hl' : l * (P * l * P⁻¹) ∈ L := mul_mem hl (hPL l hl)
  have e : (q * l * P) ^ 2 = q * (l * (P * q * P⁻¹) * l⁻¹) * (l * (P * l * P⁻¹)) := by
    calc (q * l * P) ^ 2 = (q * l * P) * (q * l * P⁻¹) := by rw [sq, hPinv]
      _ = _ := by group
  rw [e] at h
  have hmem : l * (P * l * P⁻¹) ∈ Q ⊓ L := by
    refine Subgroup.mem_inf.2 ⟨?_, hl'⟩
    rw [eq_inv_of_mul_eq_one_right h]
    exact inv_mem hq'
  rw [hQL, Subgroup.mem_bot] at hmem
  calc (l * P) ^ 2 = l * (P * l * P⁻¹) * (P * P) := by rw [sq]; group
    _ = 1 := by rw [hmem, hPP, mul_one]

theorem mem_or_eq_mul_of_mem_sup_zpowers {G : Subgroup M} {P : M}
    (hPG : ∀ g ∈ G, P * g * P⁻¹ ∈ G) (hPP : P * P = 1) {j : M}
    (hj : j ∈ G ⊔ Subgroup.zpowers P) : j ∈ G ∨ ∃ a ∈ G, j = a * P := by
  have hPinv : P⁻¹ = P := (eq_inv_of_mul_eq_one_left hPP).symm
  let S : Subgroup M :=
    { carrier := {x | x ∈ G ∨ ∃ a ∈ G, x = a * P}
      mul_mem' := by
        rintro _ _ (hx | ⟨a, ha, rfl⟩) (hy | ⟨b, hb, rfl⟩)
        · exact Or.inl (mul_mem hx hy)
        · exact Or.inr ⟨_ * b, mul_mem hx hb, by group⟩
        · refine Or.inr ⟨a * (P * _ * P⁻¹), mul_mem ha (hPG _ hy), ?_⟩
          group
        · refine Or.inl ?_
          have : a * P * (b * P) = a * (P * b * P⁻¹) := by
            rw [hPinv]
            group
          rw [this]
          exact mul_mem ha (hPG b hb)
      one_mem' := Or.inl (one_mem _)
      inv_mem' := by
        rintro _ (hx | ⟨a, ha, rfl⟩)
        · exact Or.inl (inv_mem hx)
        · refine Or.inr ⟨P * a⁻¹ * P⁻¹, hPG _ (inv_mem ha), ?_⟩
          calc (a * P)⁻¹ = P⁻¹ * a⁻¹ := by group
            _ = P * a⁻¹ * P⁻¹ * P := by rw [hPinv, mul_assoc (P * a⁻¹), hPP, mul_one] }
  have hle : G ⊔ Subgroup.zpowers P ≤ S :=
    sup_le (fun g hg => Or.inl hg) ((Subgroup.zpowers_le).2 (Or.inr ⟨1, one_mem _, by group⟩))
  exact hle hj

theorem exists_conj_eq_mul_of_sylow [Finite M] {G U : Subgroup M} {P : M} (hUG : U ≤ G)
    (hUS : ∃ S : Sylow 2 ↥G, (S : Subgroup ↥G) = U.subgroupOf G)
    (hPG : ∀ g ∈ G, P * g * P⁻¹ ∈ G) (hPU : ∀ u ∈ U, P * u * P⁻¹ ∈ U) (hPP : P * P = 1)
    (hPnG : P ∉ G) {a : M} (ha : a ∈ G) (hsq : (a * P) ^ 2 = 1) :
    ∃ g ∈ G, ∃ u ∈ U, g * (a * P) * g⁻¹ = u * P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := hUS
  have hPinv : P⁻¹ = P := (eq_inv_of_mul_eq_one_left hPP).symm
  have hUp : ∀ u ∈ U, ∃ n : ℕ, u ^ 2 ^ n = 1 := by
    intro u hu
    have hu' : (⟨u, hUG hu⟩ : G) ∈ (S₀ : Subgroup ↥G) := by
      rw [hS₀]
      exact hu
    obtain ⟨n, hn⟩ := S₀.isPGroup' ⟨_, hu'⟩
    exact ⟨n, by simpa using congrArg (fun x : (S₀ : Subgroup ↥G) => ((x : G) : M)) hn⟩
  set H := G ⊔ Subgroup.zpowers P with hH
  set S := U ⊔ Subgroup.zpowers P with hS
  have hSH : S ≤ H := sup_le_sup_right hUG _
  have hPS : P ∈ S := Subgroup.mem_sup_right (Subgroup.mem_zpowers P)
  have hPH : P ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers P)
  have hSmem := fun {x : M} (hx : x ∈ S) => mem_or_eq_mul_of_mem_sup_zpowers hPU hPP hx
  have hHmem := fun {x : M} (hx : x ∈ H) => mem_or_eq_mul_of_mem_sup_zpowers hPG hPP hx
  have hSp : IsPGroup 2 ↥(S.subgroupOf H) := by
    intro x
    rcases hSmem (Subgroup.mem_subgroupOf.1 x.2) with hx | ⟨u, hu, hxu⟩
    · obtain ⟨n, hn⟩ := hUp _ hx
      exact ⟨n, Subtype.ext (Subtype.ext (by simpa using hn))⟩
    · have hsq' : ((x : H) : M) ^ 2 = u * (P * u * P⁻¹) := by
        rw [hxu, sq, hPinv]
        group
      obtain ⟨n, hn⟩ := hUp _ (mul_mem hu (hPU u hu))
      refine ⟨n + 1, Subtype.ext (Subtype.ext ?_)⟩
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [pow_succ', pow_mul, hsq', hn]
  obtain ⟨T, hST⟩ := hSp.exists_le_sylow
  have hTG : ∀ x : H, x ∈ (T : Subgroup ↥H) → (x : M) ∈ G → (x : M) ∈ U := by
    intro x hxT hxG
    set TG : Subgroup ↥G := ((T : Subgroup ↥H).map H.subtype).subgroupOf G
    have hTGp : IsPGroup 2 ↥TG := by
      intro y
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_subgroupOf.1 y.2
      obtain ⟨n, hn⟩ := T.isPGroup' ⟨z, hz⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg (fun w : (T : Subgroup ↥H) => ((w : H) : M)) hn
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
      rw [← hzy]
      simpa using this
    have hle : (S₀ : Subgroup ↥G) ≤ TG := by
      rw [hS₀]
      intro y hy
      have hyS : (⟨(y : M), hSH (Subgroup.mem_sup_left hy)⟩ : H) ∈ S.subgroupOf H :=
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left hy)
      exact Subgroup.mem_subgroupOf.2 ⟨_, hST hyS, rfl⟩
    have heq := S₀.3 hTGp hle
    have hx' : (⟨(x : M), hxG⟩ : G) ∈ TG := Subgroup.mem_subgroupOf.2 ⟨x, hxT, rfl⟩
    rw [heq, hS₀] at hx'
    exact hx'
  have hTS : (T : Subgroup ↥H) ≤ S.subgroupOf H := by
    intro x hxT
    rw [Subgroup.mem_subgroupOf]
    rcases hHmem x.2 with hxG | ⟨g, hg, hxg⟩
    · exact Subgroup.mem_sup_left (hTG x hxT hxG)
    · have hP' : (⟨P, hPH⟩ : H) ∈ (T : Subgroup ↥H) :=
        hST (Subgroup.mem_subgroupOf.2 hPS)
      have hxP := mul_mem hxT (inv_mem hP')
      have hxP' : ((x * (⟨P, hPH⟩ : H)⁻¹ : H) : M) = g := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hxg, mul_inv_cancel_right]
      have hgU : g ∈ U := hxP' ▸ hTG _ hxP (by rw [hxP']; exact hg)
      rw [hxg]
      exact mul_mem (Subgroup.mem_sup_left hgU) hPS
  have hTeq : (T : Subgroup ↥H) = S.subgroupOf H := le_antisymm hTS hST
  have hjH : a * P ∈ H := mul_mem (Subgroup.mem_sup_left ha) hPH
  have hj2 : (⟨a * P, hjH⟩ : H) ^ 2 = 1 := Subtype.ext (by simpa using hsq)
  have hjp : IsPGroup 2 ↥(Subgroup.zpowers (⟨a * P, hjH⟩ : H)) := by
    rintro ⟨x, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hj2, one_zpow]
  obtain ⟨T₂, hT₂⟩ := hjp.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (↥H) T T₂
  have hjT₂ : (⟨a * P, hjH⟩ : H) ∈ ((y • T : Sylow 2 ↥H) : Subgroup ↥H) := by
    rw [hy]
    exact hT₂ (Subgroup.mem_zpowers _)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hTeq,
    ← map_inv, MulAut.smul_def, MulAut.conj_apply, Subgroup.mem_subgroupOf] at hjT₂
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hjT₂
  obtain ⟨g, hg, hgS⟩ : ∃ g ∈ G, g * (a * P) * g⁻¹ ∈ S := by
    rcases hHmem y.2 with hyG | ⟨g₀, hg₀, hy₀⟩
    · exact ⟨(y : M)⁻¹, inv_mem hyG, by rwa [inv_inv]⟩
    · refine ⟨g₀⁻¹, inv_mem hg₀, ?_⟩
      have h1 := mul_mem (mul_mem hPS hjT₂) (inv_mem hPS)
      rw [hy₀] at h1
      have e : P * ((g₀ * P)⁻¹ * (a * P) * (g₀ * P)) * P⁻¹ = g₀⁻¹ * (a * P) * g₀⁻¹⁻¹ := by
        group
      rwa [e] at h1
  refine ⟨g, hg, ?_⟩
  have hb : g * a * (P * g⁻¹ * P⁻¹) ∈ G := mul_mem (mul_mem hg ha) (hPG _ (inv_mem hg))
  have e : g * (a * P) * g⁻¹ = g * a * (P * g⁻¹ * P⁻¹) * P := by group
  rcases hSmem hgS with hU | ⟨u, hu, hu'⟩
  · exfalso
    apply hPnG
    have : P = (g * a * (P * g⁻¹ * P⁻¹))⁻¹ * (g * (a * P) * g⁻¹) := by rw [e]; group
    rw [this]
    exact mul_mem (inv_mem hb) (hUG hU)
  · exact ⟨u, hu, hu'⟩

end Generic

section Involution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphRootSL2

variable {E : Type} [Field E] [Finite E] {F₀ : Type} [Field F₀] [Finite F₀]

theorem exists_conj_eq_theta
    (h2 : (2 : E) = 0) (ι : F₀ →+* E) {x : ModGL TwistTag.E6.tag E}
    (hx : x ∈ thetaRankOneGroup ι) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ y ∈ thetaRankOneGroup ι, y * x * y⁻¹ = pinnedX TwistTag.E6.tag E e6HighestRoot 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2' := two_eq_zero_of_map ι h2
  have hRX : thetaRootGroup ι ≤ thetaRankOneGroup ι := le_sup_left
  have hc : Nat.card ((thetaRootGroup ι).subgroupOf (thetaRankOneGroup ι)) = Nat.card F₀ :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv).trans (card_thetaRootGroup ι)
  obtain ⟨hp, hi⟩ := E6GraphRootSL2.isPGroup_and_not_dvd_index h2 ι hc
  have hx2' : (⟨x, hx⟩ : thetaRankOneGroup ι) ^ 2 = 1 := Subtype.ext (by simpa [sq] using hx2)
  have hxp : IsPGroup 2 ↥(Subgroup.zpowers (⟨x, hx⟩ : thetaRankOneGroup ι)) := by
    rintro ⟨w, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2', one_zpow]
  obtain ⟨T, hT⟩ := hxp.exists_le_sylow
  obtain ⟨z, hz⟩ := MulAction.exists_smul_eq (↥(thetaRankOneGroup ι)) T (hp.toSylow hi)
  have hmem : (⟨x, hx⟩ : thetaRankOneGroup ι) ∈ (T : Subgroup ↥(thetaRankOneGroup ι)) :=
    hT (Subgroup.mem_zpowers _)
  have h1 : MulAut.conj z • (⟨x, hx⟩ : thetaRankOneGroup ι) ∈
      ((z • T : Sylow 2 ↥(thetaRankOneGroup ι)) : Subgroup ↥(thetaRankOneGroup ι)) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hmem
  rw [hz, IsPGroup.toSylow_coe, MulAut.smul_def, MulAut.conj_apply,
    Subgroup.mem_subgroupOf] at h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  obtain ⟨c, hcz⟩ := (mem_thetaRootGroup ι).1 h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, pinnedX_zero] at hcz
    apply hx1
    have := congrArg (fun w => (z : ModGL TwistTag.E6.tag E)⁻¹ * w * z) hcz
    simpa [mul_assoc] using this.symm
  obtain ⟨b, hb⟩ := exists_sq_eq_of_two h2' (Units.mk0 c hc0)⁻¹
  have hb' : (b : F₀) ^ 2 * c = 1 := by
    have := congrArg (fun u : F₀ˣ => (u : F₀)) hb
    simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0] at this
    rw [this, inv_mul_cancel₀ hc0]
  have hhX : rootTorusSL2 TwistTag.E6.tag E e6HighestRoot (Units.map ι.toMonoidHom b) ∈
      thetaRankOneGroup ι :=
    thetaTorus_le_thetaRankOneGroup h2 ι ((mem_thetaTorus ι).2 ⟨b, rfl⟩)
  refine ⟨rootTorusSL2 TwistTag.E6.tag E e6HighestRoot (Units.map ι.toMonoidHom b) * z,
    mul_mem hhX z.2, ?_⟩
  calc rootTorusSL2 TwistTag.E6.tag E e6HighestRoot (Units.map ι.toMonoidHom b) * z * x *
        (rootTorusSL2 TwistTag.E6.tag E e6HighestRoot (Units.map ι.toMonoidHom b) * z)⁻¹ =
        rootTorusSL2 TwistTag.E6.tag E e6HighestRoot (Units.map ι.toMonoidHom b) *
          (z * x * (z : ModGL TwistTag.E6.tag E)⁻¹) *
          (rootTorusSL2 TwistTag.E6.tag E e6HighestRoot (Units.map ι.toMonoidHom b))⁻¹ := by
        group
    _ = _ := by rw [← hcz, rootTorusSL2_conj_pinnedX_map h2 ι, hb', map_one]

end Involution

end CFSG.LieType.Chevalley.E6GraphInnerCoset
