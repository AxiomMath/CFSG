module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialQuotient
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphisms
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

variable {G : Type*} [Group G]

theorem exists_zpow_of_mem_normalizer {W : Subgroup G} (hW : IsCyclic W) {c : G}
    (hc : c ∈ Subgroup.normalizer (W : Set G)) :
    ∃ k : ℤ, ∀ w ∈ W, c * w * c⁻¹ = w ^ k := by
  obtain ⟨g, hg⟩ := hW.exists_generator
  have hgen : ∀ w ∈ W, ∃ k : ℤ, w = (g : G) ^ k := by
    intro w hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨w, hw⟩)
    exact ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
  have hcg : c * (g : G) * c⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hc g).mp g.2
  obtain ⟨k, hk⟩ := hgen _ hcg
  refine ⟨k, fun w hw => ?_⟩
  obtain ⟨j, rfl⟩ := hgen w hw
  rw [← conj_zpow, hk, ← zpow_mul, ← zpow_mul, mul_comm]

theorem inv_commutator_mem_centralizer_of_isCyclic {W : Subgroup G} (hW : IsCyclic W)
    {a b : G} (ha : a ∈ Subgroup.normalizer (W : Set G))
    (hb : b ∈ Subgroup.normalizer (W : Set G)) :
    a⁻¹ * b⁻¹ * a * b ∈ Subgroup.centralizer (W : Set G) := by
  obtain ⟨i, hi⟩ := exists_zpow_of_mem_normalizer hW ha
  obtain ⟨j, hj⟩ := exists_zpow_of_mem_normalizer hW hb
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h1 : (a * b) * w * (a * b)⁻¹ = (b * a) * w * (b * a)⁻¹ := by
    calc (a * b) * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by group
      _ = a * w ^ j * a⁻¹ := by rw [hj w hw]
      _ = (a * w * a⁻¹) ^ j := by rw [conj_zpow]
      _ = (w ^ i) ^ j := by rw [hi w hw]
      _ = (w ^ j) ^ i := by rw [← zpow_mul, ← zpow_mul, mul_comm]
      _ = (b * w * b⁻¹) ^ i := by rw [hj w hw]
      _ = b * w ^ i * b⁻¹ := by rw [conj_zpow]
      _ = b * (a * w * a⁻¹) * b⁻¹ := by rw [hi w hw]
      _ = (b * a) * w * (b * a)⁻¹ := by group
  calc w * (a⁻¹ * b⁻¹ * a * b) = (b * a)⁻¹ * ((b * a) * w * (b * a)⁻¹) * (a * b) := by group
    _ = (b * a)⁻¹ * ((a * b) * w * (a * b)⁻¹) * (a * b) := by rw [h1]
    _ = a⁻¹ * b⁻¹ * a * b * w := by group

theorem commutator_mem_centralizer_of_isCyclic {W : Subgroup G} (hW : IsCyclic W)
    {a b : G} (ha : a ∈ Subgroup.normalizer (W : Set G))
    (hb : b ∈ Subgroup.normalizer (W : Set G)) :
    a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
  have h := inv_commutator_mem_centralizer_of_isCyclic hW (Subgroup.inv_mem _ ha)
    (Subgroup.inv_mem _ hb)
  simpa only [inv_inv] using h

theorem dichotomy_of_mem_sup {X : Subgroup G} {d h : G} (hd : ∀ x ∈ X, d * x * d⁻¹ = x⁻¹)
    (hh : h ∈ Subgroup.centralizer (X : Set G) ⊔ Subgroup.zpowers d) :
    (∀ x ∈ X, h * x * h⁻¹ = x) ∨ (∀ x ∈ X, h * x * h⁻¹ = x⁻¹) := by
  let S : Subgroup G :=
    { carrier := {h | (∀ x ∈ X, h * x * h⁻¹ = x) ∨ (∀ x ∈ X, h * x * h⁻¹ = x⁻¹)}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · left
          intro x hx
          calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
            _ = x := by rw [hb x hx, ha x hx]
        · right
          intro x hx
          calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
            _ = x⁻¹ := by rw [hb x hx, ha x⁻¹ (X.inv_mem hx)]
        · right
          intro x hx
          calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
            _ = x⁻¹ := by rw [hb x hx, ha x hx]
        · left
          intro x hx
          calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
            _ = x := by rw [hb x hx, ha x⁻¹ (X.inv_mem hx), inv_inv]
      one_mem' := Or.inl fun x _ => by group
      inv_mem' := by
        rintro a (ha | ha)
        · left
          intro x hx
          calc a⁻¹ * x * a⁻¹⁻¹ = a⁻¹ * (a * x * a⁻¹) * a := by rw [ha x hx, inv_inv]
            _ = x := by group
        · right
          intro x hx
          calc a⁻¹ * x * a⁻¹⁻¹ = a⁻¹ * (a * x⁻¹ * a⁻¹) * a := by
                rw [ha x⁻¹ (X.inv_mem hx), inv_inv, inv_inv]
            _ = x⁻¹ := by group }
  have hle : Subgroup.centralizer (X : Set G) ⊔ Subgroup.zpowers d ≤ S := by
    refine sup_le ?_ ?_
    · intro c hc
      left
      intro x hx
      rw [(Subgroup.mem_centralizer_iff.mp hc x hx).symm]
      group
    · rw [Subgroup.zpowers_le]
      exact Or.inr hd
  exact hle hh

theorem conj_sq_eq_of_mem_normalizer {d s x : G} (hd4 : orderOf d = 4) (hs : s * s = 1)
    (hsd : s * d * s⁻¹ = d⁻¹)
    (hx : x ∈ Subgroup.normalizer
      ((Subgroup.zpowers d ⊔ Subgroup.zpowers s : Subgroup G) : Set G)) :
    x * (d * d) * x⁻¹ = d * d := by
  have hdD : d ∈ (Subgroup.zpowers d ⊔ Subgroup.zpowers s : Subgroup G) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
  have hxd := (Subgroup.mem_normalizer_iff.mp hx d).mp hdD
  have ho : orderOf (x * d * x⁻¹) = 4 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hd4]
  obtain ⟨i, hi | hi⟩ := mem_dihedral_cases hs hsd hxd
  · have hiodd : Odd i := by
      rcases Int.even_or_odd i with ⟨j, rfl⟩ | h
      · exfalso
        have h2 : (d ^ (j + j)) ^ 2 = 1 := by
          rw [← zpow_natCast, ← zpow_mul, show (j + j) * ((2 : ℕ) : ℤ) = 4 * j by push_cast; ring,
            zpow_mul, show ((4 : ℤ)) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast,
            ← hd4, pow_orderOf_eq_one, one_zpow]
        have := orderOf_dvd_of_pow_eq_one h2
        rw [← hi, ho] at this
        norm_num at this
      · exact h
    obtain ⟨k, rfl⟩ := hiodd
    calc x * (d * d) * x⁻¹ = (x * d * x⁻¹) * (x * d * x⁻¹) := by group
      _ = d ^ (2 * k + 1) * d ^ (2 * k + 1) := by rw [hi]
      _ = d ^ (4 * k) * (d * d) := by
          rw [← zpow_add, show 2 * k + 1 + (2 * k + 1) = 4 * k + 2 by ring, zpow_add,
            show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]
      _ = d * d := by
          rw [zpow_mul, show ((4 : ℤ)) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, ← hd4,
            pow_orderOf_eq_one, one_zpow, one_mul]
  · exfalso
    have h2 := zpow_mul_sq hs hsd i
    have := orderOf_dvd_of_pow_eq_one (show (d ^ i * s) ^ 2 = 1 by rw [pow_two]; exact h2)
    rw [← hi, ho] at this
    norm_num at this

theorem exists_sylow_eq_of_maximal [Finite G] (S : Sylow 2 G) {t : G}
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t})
    (hS4 : ∀ x ∈ (S : Subgroup G), orderOf x = 4 → x ^ 2 = t)
    (F P₀ : Subgroup G) (hP₀F : P₀ ≤ F) (hP₀ : IsPGroup 2 P₀) {d : G} (hdP : d ∈ P₀)
    (hd4 : orderOf d = 4) (hd2 : d ^ 2 = t)
    (hmax : ∀ T : Subgroup G, IsPGroup 2 T → P₀ ≤ T →
      T ≤ Subgroup.centralizer {t} ⊓ F → T = P₀) :
    ∃ P : Sylow 2 F, (P : Subgroup F).map F.subtype = P₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP₀p : IsPGroup 2 (P₀.subgroupOf F) :=
    hP₀.of_equiv (Subgroup.subgroupOfEquivOfLe hP₀F).symm
  obtain ⟨T, hT⟩ := hP₀p.exists_le_sylow
  have hTp : IsPGroup 2 ((T : Subgroup F).map F.subtype) := T.isPGroup'.map _
  obtain ⟨S', hS'⟩ := hTp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S'
  have hmemS : ∀ x ∈ (T : Subgroup F).map F.subtype, g⁻¹ * x * g ∈ (S : Subgroup G) := by
    intro x hx
    have h : x ∈ ((g • S : Sylow 2 G) : Subgroup G) := hg ▸ hS' hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h
    simpa [MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply] using h
  have hdT : d ∈ (T : Subgroup F).map F.subtype :=
    ⟨⟨d, hP₀F hdP⟩, hT (show (⟨d, hP₀F hdP⟩ : F) ∈ P₀.subgroupOf F from hdP), rfl⟩
  have hgC : g ∈ Subgroup.centralizer {t} := by
    have hy := hmemS d hdT
    have hy4 : orderOf (g⁻¹ * d * g) = 4 := by
      have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) d
      rw [MulAut.conj_apply, inv_inv] at h
      rw [h, hd4]
    have hy2 := hS4 _ hy hy4
    have hconj : g⁻¹ * t * g = t := by
      calc g⁻¹ * t * g = g⁻¹ * d ^ 2 * g := by rw [hd2]
        _ = (g⁻¹ * d * g) ^ 2 := by rw [sq, sq]; group
        _ = t := hy2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * t = g * (g⁻¹ * t * g) := by rw [hconj]
      _ = t * g := by group
  have hTC : (T : Subgroup F).map F.subtype ≤ Subgroup.centralizer {t} ⊓ F := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hxS := hSC (hmemS x hx)
      rw [Subgroup.mem_centralizer_singleton_iff] at hxS hgC ⊢
      have hg' : g⁻¹ * t = t * g⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgC, mul_assoc, mul_inv_cancel, mul_one]
      calc x * t = g * (g⁻¹ * x * g) * (g⁻¹ * t) := by group
        _ = g * (g⁻¹ * x * g) * (t * g⁻¹) := by rw [hg']
        _ = g * ((g⁻¹ * x * g) * t) * g⁻¹ := by group
        _ = g * (t * (g⁻¹ * x * g)) * g⁻¹ := by rw [hxS]
        _ = (g * t) * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = (t * g) * (g⁻¹ * x * g) * g⁻¹ := by rw [hgC]
        _ = t * x := by group
    · obtain ⟨y, -, rfl⟩ := hx
      exact y.2
  have hP₀T : P₀ ≤ (T : Subgroup F).map F.subtype := by
    intro x hx
    exact ⟨⟨x, hP₀F hx⟩, hT (show (⟨x, hP₀F hx⟩ : F) ∈ P₀.subgroupOf F from hx), rfl⟩
  exact ⟨T, hmax _ hTp hP₀T hTC⟩

theorem exists_commutator_three_cycle {V : Subgroup G} (hV : IsKleinFour V) {t s : G}
    (htV : t ∈ V) (hsV : s ∈ V) (ht1 : t ≠ 1) (hs1 : s ≠ 1) (hts : t ≠ s)
    (hsurj : Function.Surjective V.normalizerMonoidHom) :
    ∃ a ∈ Subgroup.normalizer (V : Set G), ∃ b ∈ Subgroup.normalizer (V : Set G),
      (a * b * a⁻¹ * b⁻¹) * t * (a * b * a⁻¹ * b⁻¹)⁻¹ = s ∧
      (a * b * a⁻¹ * b⁻¹) * s * (a * b * a⁻¹ * b⁻¹)⁻¹ = t * s := by
  classical
  obtain ⟨⟨e, he⟩, -, -, -⟩ := CFSG.Semidihedral.Local.kleinFour_automorphism_action (V := V)
  have htsV : t * s ∈ V := V.mul_mem htV hsV
  have hts1 : t * s ≠ 1 := by
    intro h
    apply hts
    have hs2 : s * s = 1 := by
      have h2 := Monoid.pow_exponent_eq_one (⟨s, hsV⟩ : V)
      rw [hV.exponent_two, pow_two] at h2
      exact congrArg Subtype.val h2
    calc t = t * s * s := by rw [mul_assoc, hs2, mul_one]
      _ = s := by rw [h, one_mul]
  let T' : {x : V // x ≠ 1} := ⟨⟨t, htV⟩, fun h => ht1 (congrArg Subtype.val h)⟩
  let S' : {x : V // x ≠ 1} := ⟨⟨s, hsV⟩, fun h => hs1 (congrArg Subtype.val h)⟩
  let U' : {x : V // x ≠ 1} := ⟨⟨t * s, htsV⟩, fun h => hts1 (congrArg Subtype.val h)⟩
  have hTS : T' ≠ S' := fun h => hts (congrArg (fun x : {x : V // x ≠ 1} => ((x : V) : G)) h)
  have hTU : T' ≠ U' := by
    intro h
    have h' : t = t * s := congrArg (fun x : {x : V // x ≠ 1} => ((x : V) : G)) h
    apply hs1
    calc s = t⁻¹ * (t * s) := by group
      _ = 1 := by rw [← h', inv_mul_cancel]
  have hSU : S' ≠ U' := by
    intro h
    have h' : s = t * s := congrArg (fun x : {x : V // x ≠ 1} => ((x : V) : G)) h
    apply ht1
    calc t = t * s * s⁻¹ := by group
      _ = 1 := by rw [← h', mul_inv_cancel]
  set α : Equiv.Perm {x : V // x ≠ 1} := Equiv.swap T' S' with hαdef
  set β : Equiv.Perm {x : V // x ≠ 1} := Equiv.swap T' U' with hβdef
  have hτT : (α * β * α⁻¹ * β⁻¹) T' = S' := by
    simp only [hαdef, hβdef, Equiv.swap_inv, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    rw [Equiv.swap_apply_of_ne_of_ne hTU.symm hSU.symm, Equiv.swap_apply_right,
      Equiv.swap_apply_left]
  have hτS : (α * β * α⁻¹ * β⁻¹) S' = U' := by
    simp only [hαdef, hβdef, Equiv.swap_inv, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hTS.symm hSU, Equiv.swap_apply_right,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hTU.symm hSU.symm]
  obtain ⟨a, ha⟩ := hsurj (e.symm α)
  obtain ⟨b, hb⟩ := hsurj (e.symm β)
  have hcomm : V.normalizerMonoidHom (a * b * a⁻¹ * b⁻¹) = e.symm (α * β * α⁻¹ * β⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ha, hb, map_mul, map_mul, map_mul, map_inv,
      map_inv]
  have hact : ∀ x : {x : V // x ≠ 1}, (a * b * a⁻¹ * b⁻¹ : G) * ((x : V) : G) *
      (a * b * a⁻¹ * b⁻¹ : G)⁻¹ = (((α * β * α⁻¹ * β⁻¹) x : V) : G) := by
    intro x
    have h1 := Subgroup.normalizerMonoidHom_apply_apply_coe V (a * b * a⁻¹ * b⁻¹) (x : V)
    rw [hcomm] at h1
    have h2 := he (e.symm (α * β * α⁻¹ * β⁻¹)) x
    rw [MulEquiv.apply_symm_apply] at h2
    rw [h2, h1]
    push_cast
    rfl
  refine ⟨a, a.2, b, b.2, ?_, ?_⟩
  · have h := hact T'
    rw [hτT] at h
    exact h
  · have h := hact S'
    rw [hτS] at h
    exact h

end CFSG.Semidihedral.FixedCoreNontrivial
