module

public import CFSG.Assembly.Defs

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Assembly

variable {G : Type*} [Group G]

theorem exists_zmodTwo_functional_vanishing_pair {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) (hA2 : ∀ a : A, a ^ 2 = 1) (hcard : 4 < Nat.card A)
    (z w : A) :
    ∃ α : Additive A →+ ZMod 2, α (Additive.ofMul z) = 0 ∧ α (Additive.ofMul w) = 0 ∧
      ∃ v : A, α (Additive.ofMul v) = 1 := by
  let _ : CommGroup A := { ‹Group A› with mul_comm := hcomm }
  let _ : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule fun x =>
    Additive.toMul.injective (by simp [hA2])
  set p : Submodule (ZMod 2) (Additive A) :=
    Submodule.span (ZMod 2) {Additive.ofMul z, Additive.ofMul w}
  have hp : p < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => ?_
    have hsurj : Function.Surjective fun cd : ZMod 2 × ZMod 2 =>
        cd.1 • Additive.ofMul z + cd.2 • Additive.ofMul w := fun x => by
      have hx : x ∈ p := by rw [htop]; exact Submodule.mem_top
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 hx
      exact ⟨(a, b), hab⟩
    have h4 := Nat.card_le_card_of_surjective _ hsurj
    simp only [Nat.card_prod, Nat.card_zmod] at h4
    change Nat.card A ≤ 2 * 2 at h4
    omega
  obtain ⟨f, hf0, hpf⟩ := Submodule.exists_le_ker_of_lt_top p hp
  obtain ⟨v, hv⟩ : ∃ v : Additive A, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (LinearMap.ext h)
  refine ⟨f.toAddMonoidHom, LinearMap.mem_ker.1 (hpf (Submodule.subset_span (by simp))),
    LinearMap.mem_ker.1 (hpf (Submodule.subset_span (by simp))), Additive.toMul v, ?_⟩
  change f v = 1
  revert hv
  generalize f v = c
  revert c
  decide

theorem conj_mem_closure_involutions {S : Subgroup G} {s : G} (hs : s ∈ S) {x : G}
    (hx : x ∈ Subgroup.closure {x : G | x ∈ S ∧ orderOf x = 2}) :
    s * x * s⁻¹ ∈ Subgroup.closure {x : G | x ∈ S ∧ orderOf x = 2} := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    refine Subgroup.subset_closure ⟨S.mul_mem (S.mul_mem hs hy.1) (S.inv_mem hs), ?_⟩
    rw [← hy.2]
    exact (SemiconjBy.orderOf_eq s (by rw [SemiconjBy]; group)).symm
  | one => simp
  | mul a b _ _ ha hb =>
    have e : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

theorem le_normalizer_closure_involutions (S : Subgroup G) :
    S ≤ Subgroup.normalizer
      ((Subgroup.closure {x : G | x ∈ S ∧ orderOf x = 2} : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_closure_involutions hs, fun h => ?_⟩
  have h' := conj_mem_closure_involutions (S.inv_mem hs) h
  have e : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
  rwa [e] at h'

theorem mem_normalizer_of_forall_conj_mem [Finite G] {A : Subgroup G} {x : G}
    (h : ∀ a ∈ A, x * a * x⁻¹ ∈ A) : x ∈ Subgroup.normalizer (A : Set G) := by
  have hle : A.map (MulAut.conj x).toMonoidHom ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  have heq := Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨h b, fun hb => ?_⟩
  rw [← heq] at hb
  obtain ⟨a, ha, hab⟩ := Subgroup.mem_map.1 hb
  have hab' : x * a * x⁻¹ = x * b * x⁻¹ := hab
  rw [mul_left_inj, mul_right_inj] at hab'
  exact hab' ▸ ha

theorem conj_mul_pow_eq (s a c : G) (k : ℕ) :
    s * (a * c ^ k) * s⁻¹ = (s * a * s⁻¹) * (s * c * s⁻¹) ^ k := by
  rw [conj_pow]
  group

theorem normalizer_fixes_shear_axis [Finite G] (S : Sylow 2 G) {A : Subgroup G}
    (hSN : (S : Subgroup G) ≤ Subgroup.normalizer (A : Set G))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hcard : 4 < Nat.card A) {z : G} (hzA : z ∈ A) (hz1 : z ≠ 1)
    (h1 : ∀ s ∈ (S : Subgroup G), ∃ ℓ : Additive A →+ ZMod 2,
      ℓ (Additive.ofMul (⟨z, hzA⟩ : A)) = 0 ∧
        ∀ a : A, s * a * s⁻¹ = a * z ^ (ℓ (Additive.ofMul a)).val)
    (h2 : ∀ ℓ : Additive A →+ ZMod 2, ℓ (Additive.ofMul (⟨z, hzA⟩ : A)) = 0 →
      ∃ s ∈ (S : Subgroup G), ∀ a : A, s * a * s⁻¹ = a * z ^ (ℓ (Additive.ofMul a)).val)
    {n : G} (hn : n ∈ Subgroup.normalizer (A : Set G)) : n * z * n⁻¹ = z := by
  classical
  set N := Subgroup.normalizer (A : Set G) with hN_def
  have hconjA : ∀ m ∈ N, ∀ a ∈ A, m * a * m⁻¹ ∈ A := fun m hm a ha =>
    (Subgroup.mem_normalizer_iff.1 hm a).1 ha
  have hsq : ∀ c ∈ A, ∀ k : ℕ, c ^ k * c ^ k = 1 := fun c hc k => by
    rw [← pow_add, ← two_mul, pow_mul, hA2 c hc, one_pow]
  by_contra hw
  set w := n * z * n⁻¹ with hw_def
  have hwA : w ∈ A := hconjA n hn z hzA
  have hw1 : w ≠ 1 := fun h => hz1 (by
    have h' : n⁻¹ * w * n = n⁻¹ * 1 * n := by rw [h]
    rwa [hw_def, mul_one, inv_mul_cancel, show n⁻¹ * (n * z * n⁻¹) * n = z by group] at h')
  obtain ⟨α, hαz, hαw, v₀, hv₀⟩ := exists_zmodTwo_functional_vanishing_pair (A := A)
    (fun a b => Subtype.ext (hcomm _ a.2 _ b.2)) (fun a => Subtype.ext (by simpa using hA2 _ a.2))
    hcard ⟨z, hzA⟩ ⟨w, hwA⟩
  let cn : A →* A := (A.normalizerMonoidHom ⟨n, hn⟩ : A ≃* A).toMonoidHom
  let α' : Additive A →+ ZMod 2 := α.comp (MonoidHom.toAdditive cn)
  have hα' : ∀ b a : A, (a : G) = n * b * n⁻¹ → α' (Additive.ofMul b) = α (Additive.ofMul a) :=
    fun b a hab => by
      change α (Additive.ofMul (cn b)) = _
      congr 2
      exact Subtype.ext ((Subgroup.normalizerMonoidHom_apply_apply_coe A ⟨n, hn⟩ b).trans hab.symm)
  obtain ⟨s, hsS, hs⟩ := h2 α hαz
  obtain ⟨s', hs'S, hs'⟩ := h2 α' (by rw [hα' _ ⟨w, hwA⟩ rfl]; exact hαw)
  set y := n * s' * n⁻¹ with hy_def
  have hy : ∀ a : A, y * a * y⁻¹ = a * w ^ (α (Additive.ofMul a)).val := fun a => by
    have hmem : n⁻¹ * a * n ∈ A := by
      simpa using hconjA n⁻¹ (N.inv_mem hn) a a.2
    have hb := hs' ⟨n⁻¹ * a * n, hmem⟩
    rw [hα' _ a (by simp only; group)] at hb
    calc y * a * y⁻¹ = n * (s' * (n⁻¹ * a * n) * s'⁻¹) * n⁻¹ := by rw [hy_def]; group
      _ = n * ((n⁻¹ * a * n) * z ^ (α (Additive.ofMul a)).val) * n⁻¹ := by
          rw [show s' * (n⁻¹ * a * n) * s'⁻¹ = (n⁻¹ * a * n) * z ^ (α (Additive.ofMul a)).val
            from hb]
      _ = a * w ^ (α (Additive.ofMul a)).val := by rw [hw_def, conj_pow]; group
  have hs_z : s * z * s⁻¹ = z := by
    have := hs ⟨z, hzA⟩
    rw [hαz, ZMod.val_zero, pow_zero, mul_one] at this
    exact this
  have hs_w : s * w * s⁻¹ = w := by
    have := hs ⟨w, hwA⟩
    rw [hαw, ZMod.val_zero, pow_zero, mul_one] at this
    exact this
  have hy_z : y * z * y⁻¹ = z := by
    have := hy ⟨z, hzA⟩
    rw [hαz, ZMod.val_zero, pow_zero, mul_one] at this
    exact this
  have hy_w : y * w * y⁻¹ = w := by
    have := hy ⟨w, hwA⟩
    rw [hαw, ZMod.val_zero, pow_zero, mul_one] at this
    exact this
  set φ := A.normalizerMonoidHom with hφ_def
  have hφ : ∀ (m : N) (a : A), ((φ m a : A) : G) = m * a * (m : G)⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe A
  set X := φ.range with hX_def
  have : Finite X := Finite.of_surjective _ φ.rangeRestrict_surjective
  set QS : Sylow 2 X := (S.subtype hSN).mapSurjective φ.rangeRestrict_surjective with hQS_def
  have hext : ∀ p q : N, (∀ a : A, (p : G) * a * (p : G)⁻¹ = q * a * (q : G)⁻¹) →
      φ.rangeRestrict p = φ.rangeRestrict q := fun p q h => by
    apply Subtype.ext
    rw [MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict]
    ext a
    rw [hφ, hφ, h]
  have hsN : s ∈ N := hSN hsS
  have hyN : y ∈ N := N.mul_mem (N.mul_mem hn (hSN hs'S)) (N.inv_mem hn)
  set xs : X := φ.rangeRestrict ⟨s, hsN⟩ with hxs_def
  set ys : X := φ.rangeRestrict ⟨y, hyN⟩ with hys_def
  have hxy : xs * ys = ys * xs := by
    rw [hxs_def, hys_def, ← map_mul, ← map_mul]
    apply hext
    intro a
    simp only [Subgroup.coe_mul, mul_inv_rev]
    have e1 : s * y * a * (y⁻¹ * s⁻¹) = s * (y * a * y⁻¹) * s⁻¹ := by group
    have e2 : y * s * a * (s⁻¹ * y⁻¹) = y * (s * a * s⁻¹) * y⁻¹ := by group
    rw [e1, e2, hy a, hs a, conj_mul_pow_eq, conj_mul_pow_eq, hs a, hs_w, hy a, hy_z,
      mul_assoc, mul_assoc,
      hcomm _ (A.pow_mem hzA _) _ (A.pow_mem hwA _)]
  have hxs2 : xs ^ 2 = 1 := by
    rw [sq, hxs_def, ← map_mul, ← map_one φ.rangeRestrict]
    apply hext
    intro a
    simp only [Subgroup.coe_mul, Subgroup.coe_one, mul_inv_rev, one_mul, inv_one, mul_one]
    have e1 : s * s * a * (s⁻¹ * s⁻¹) = s * (s * a * s⁻¹) * s⁻¹ := by group
    rw [e1, hs a, conj_mul_pow_eq, hs a, hs_z, mul_assoc, hsq z hzA, mul_one]
  have hys2 : ys ^ 2 = 1 := by
    rw [sq, hys_def, ← map_mul, ← map_one φ.rangeRestrict]
    apply hext
    intro a
    simp only [Subgroup.coe_mul, Subgroup.coe_one, mul_inv_rev, one_mul, inv_one, mul_one]
    have e1 : y * y * a * (y⁻¹ * y⁻¹) = y * (y * a * y⁻¹) * y⁻¹ := by group
    rw [e1, hy a, conj_mul_pow_eq, hy a, hy_w, mul_assoc, hsq w hwA, mul_one]
  have hzp : ∀ u : X, u ^ 2 = 1 → IsPGroup 2 (Subgroup.zpowers u) := fun u hu => by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (orderOf_dvd_of_pow_eq_one (by simpa using hu) : orderOf u ∣ 2 ^ 1)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hP : IsPGroup 2 ↥(Subgroup.zpowers xs ⊔ Subgroup.zpowers ys) := by
    refine IsPGroup.to_sup_of_normal_right' (hzp xs hxs2) (hzp ys hys2) ?_
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact ((Commute.zpow_left (show Commute ys xs from hxy.symm) k).eq)
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq X QS Q
  obtain ⟨m, hm⟩ := φ.rangeRestrict_surjective c
  have hshape : ∀ u ∈ ((c • QS : Sylow 2 X) : Subgroup X), ∀ ε ∈ A, ε ≠ 1 →
      (((u : MulAut A) v₀ : A) : G) = v₀ * ε → ε = m * z * (m : G)⁻¹ := by
    intro u hu ε hεA hε1 hεu
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      hQS_def, Sylow.coe_mapSurjective, Sylow.coe_subtype] at hu
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 hu
    have htS : (t : G) ∈ (S : Subgroup G) := Subgroup.mem_subgroupOf.1 ht
    have hu' : u = φ.rangeRestrict (m * t * m⁻¹) := by
      rw [map_mul, map_mul, map_inv, hm, hte, MulAut.smul_def, MulAut.conj_inv_apply]
      group
    obtain ⟨ℓ, -, hℓ⟩ := h1 t htS
    have hmem : (m : G)⁻¹ * v₀ * m ∈ A := by
      simpa using hconjA (m : G)⁻¹ (N.inv_mem m.2) v₀ v₀.2
    have hb := hℓ ⟨(m : G)⁻¹ * v₀ * m, hmem⟩
    set k := (ℓ (Additive.ofMul (⟨(m : G)⁻¹ * v₀ * m, hmem⟩ : A))).val with hk_def
    have hk2 : k < 2 := ZMod.val_lt _
    rw [hu', MonoidHom.coe_rangeRestrict, hφ] at hεu
    have hεk : ε = (m * z * (m : G)⁻¹) ^ k := by
      have e : (((m * t * m⁻¹ : N) : G)) * v₀ * ((m * t * m⁻¹ : N) : G)⁻¹ =
          v₀ * (m * z * (m : G)⁻¹) ^ k := by
        calc (((m * t * m⁻¹ : N) : G)) * v₀ * ((m * t * m⁻¹ : N) : G)⁻¹
            = m * (t * ((m : G)⁻¹ * v₀ * m) * (t : G)⁻¹) * (m : G)⁻¹ := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
          _ = m * (((m : G)⁻¹ * v₀ * m) * z ^ k) * (m : G)⁻¹ := by
              rw [show (t : G) * ((m : G)⁻¹ * v₀ * m) * (t : G)⁻¹ =
                ((m : G)⁻¹ * v₀ * m) * z ^ k from hb]
          _ = v₀ * (m * z * (m : G)⁻¹) ^ k := by rw [conj_pow]; group
      rw [e] at hεu
      exact (mul_left_cancel hεu).symm
    rcases (by omega : k = 0 ∨ k = 1) with h0 | h0
    · rw [h0, pow_zero] at hεk
      exact absurd hεk hε1
    · rwa [h0, pow_one] at hεk
  have hxsQ : xs ∈ ((c • QS : Sylow 2 X) : Subgroup X) :=
    hPQ (Subgroup.mem_sup_left (Subgroup.mem_zpowers xs))
  have hysQ : ys ∈ ((c • QS : Sylow 2 X) : Subgroup X) :=
    hPQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers ys))
  have hxv : (((xs : MulAut A) v₀ : A) : G) = v₀ * z := by
    rw [hxs_def, MonoidHom.coe_rangeRestrict, hφ]
    change s * v₀ * s⁻¹ = _
    rw [hs v₀, hv₀, show (1 : ZMod 2).val = 1 from rfl, pow_one]
  have hyv : (((ys : MulAut A) v₀ : A) : G) = v₀ * w := by
    rw [hys_def, MonoidHom.coe_rangeRestrict, hφ]
    change y * v₀ * y⁻¹ = _
    rw [hy v₀, hv₀, show (1 : ZMod 2).val = 1 from rfl, pow_one]
  have e1 := hshape xs hxsQ z hzA hz1 hxv
  have e2 := hshape ys hysQ w hwA hw1 hyv
  exact hw (e2.trans e1.symm)

theorem conj_mem_eq_of_normalizer_fixes [Finite G] (S : Sylow 2 G) {A : Subgroup G}
    (hinv : ∀ x ∈ (S : Subgroup G), orderOf x = 2 → x ∈ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    {z : G} (hzA : z ∈ A) (hz1 : z ≠ 1)
    (hN : ∀ n ∈ Subgroup.normalizer (A : Set G), n * z * n⁻¹ = z)
    {g : G} (hg : g⁻¹ * z * g ∈ (S : Subgroup G)) : g⁻¹ * z * g = z := by
  set y := g⁻¹ * z * g with hy_def
  have hzo : orderOf z = 2 := orderOf_eq_prime (hA2 z hzA) hz1
  have hyo : orderOf y = 2 := by
    rw [← hzo]
    exact (SemiconjBy.orderOf_eq g⁻¹ (by rw [SemiconjBy, hy_def]; group)).symm
  have hyA : y ∈ A := hinv y hg hyo
  set C := Subgroup.centralizer ({y} : Set G) with hC_def
  have hAC : ∀ a ∈ A, a ∈ C := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm a ha y hyA)
  have hA'C : ∀ a ∈ A, g⁻¹ * a * g ∈ C := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (by
      rw [hy_def]
      calc g⁻¹ * a * g * (g⁻¹ * z * g) = g⁻¹ * (a * z) * g := by group
        _ = g⁻¹ * (z * a) * g := by rw [hcomm a ha z hzA]
        _ = g⁻¹ * z * g * (g⁻¹ * a * g) := by group)
  have h2grp : ∀ H : Subgroup C, (∀ x ∈ H, ((x : C) : G) ^ 2 = 1) → IsPGroup 2 H :=
    fun H hH x => ⟨1, Subtype.ext (Subtype.ext (by simpa using hH x x.2))⟩
  have hA₁ : IsPGroup 2 (A.subgroupOf C) :=
    h2grp _ fun x hx => hA2 _ (Subgroup.mem_subgroupOf.1 hx)
  have hA₂ : IsPGroup 2 ((A.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf C) :=
    h2grp _ fun x hx => by
      obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
      have hax' : g⁻¹ * a * g⁻¹⁻¹ = (x : G) := hax
      rw [← hax', conj_pow, hA2 a ha]
      group
  obtain ⟨S₁, hS₁⟩ := hA₁.exists_le_sylow
  obtain ⟨S₂, hS₂⟩ := hA₂.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C S₂ S₁
  have hT₀ : IsPGroup 2 ((S₁ : Subgroup C).map C.subtype) := S₁.isPGroup'.map _
  obtain ⟨T, hT⟩ := hT₀.exists_le_sylow
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq G S T
  have hTA : ∀ u ∈ ((h • S : Sylow 2 G) : Subgroup G), u ^ 2 = 1 → h⁻¹ * u * h ∈ A := by
    intro u hu hu2
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hu
    have hu' : h⁻¹ * u * h ∈ (S : Subgroup G) := by
      rw [MulAut.smul_def, MulAut.conj_inv_apply] at hu
      exact hu
    by_cases h1 : h⁻¹ * u * h = 1
    · rw [h1]
      exact A.one_mem
    · refine hinv _ hu' (orderOf_eq_prime ?_ h1)
      rw [show h⁻¹ * u * h = h⁻¹ * u * h⁻¹⁻¹ by rw [inv_inv], conj_pow, hu2]
      group
  have hAT : ∀ a ∈ A, a ∈ ((h • S : Sylow 2 G) : Subgroup G) := fun a ha =>
    hT ⟨⟨a, hAC a ha⟩, hS₁ (Subgroup.mem_subgroupOf.2 ha), rfl⟩
  have hkT : ∀ a ∈ A, (c : G) * g⁻¹ * a * ((c : G) * g⁻¹)⁻¹ ∈
      ((h • S : Sylow 2 G) : Subgroup G) := by
    intro a ha
    have hmem : (⟨g⁻¹ * a * g, hA'C a ha⟩ : C) ∈ (S₂ : Subgroup C) :=
      hS₂ (Subgroup.mem_subgroupOf.2 ⟨a, ha, by
        change g⁻¹ * a * g⁻¹⁻¹ = g⁻¹ * a * g
        rw [inv_inv]⟩)
    have hmem' : MulAut.conj c • (⟨g⁻¹ * a * g, hA'C a ha⟩ : C) ∈ (S₁ : Subgroup C) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hmem
    refine hT ⟨_, hmem', ?_⟩
    rw [MulAut.smul_def, MulAut.conj_apply]
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hh : h⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    mem_normalizer_of_forall_conj_mem fun a ha => by
      rw [inv_inv]
      exact hTA a (hAT a ha) (hA2 a ha)
  have hhk : h⁻¹ * ((c : G) * g⁻¹) ∈ Subgroup.normalizer (A : Set G) :=
    mem_normalizer_of_forall_conj_mem fun a ha => by
      have hsq : ((c : G) * g⁻¹ * a * ((c : G) * g⁻¹)⁻¹) ^ 2 = 1 := by
        rw [conj_pow, hA2 a ha]
        group
      have := hTA _ (hkT a ha) hsq
      rw [show h⁻¹ * ((c : G) * g⁻¹) * a * (h⁻¹ * ((c : G) * g⁻¹))⁻¹ =
        h⁻¹ * ((c : G) * g⁻¹ * a * ((c : G) * g⁻¹)⁻¹) * h by group]
      exact this
  have hk : (c : G) * g⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hhk
    rwa [inv_inv, mul_inv_cancel_left] at this
  have hkz := hN _ hk
  have hcy : (c : G) * y = y * c := Subgroup.mem_centralizer_singleton_iff.1 c.2
  calc y = (c : G) * y * (c : G)⁻¹ := by rw [hcy, mul_inv_cancel_right]
    _ = (c : G) * g⁻¹ * z * ((c : G) * g⁻¹)⁻¹ := by rw [hy_def]; group
    _ = z := hkz

theorem even_four_dimensional_involution_shears_isolate_axis [Finite G] (S : Sylow 2 G)
    {A : Subgroup G}
    (hA : A = Subgroup.closure {x : G | x ∈ (S : Subgroup G) ∧ orderOf x = 2})
    (hAe : IsElemAbelian 2 A) (hA16 : Nat.card A = 16) {z : G} (hzA : z ∈ A) (hz1 : z ≠ 1)
    (hshear : {f : A → A | ∃ s ∈ (S : Subgroup G), ∀ a : A, (f a : G) = s * a * s⁻¹} =
      {f : A → A | ∃ ℓ : Additive A →+ ZMod 2, ℓ (Additive.ofMul (⟨z, hzA⟩ : A)) = 0 ∧
        ∀ a : A, (f a : G) = a * z ^ (ℓ (Additive.ofMul a)).val}) :
    z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype ∧
      Set.range (fun g : G => g⁻¹ * z * g) ∩ (S : Set G) = {z} := by
  obtain ⟨hAc, hA2⟩ := hAe
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAS : A ≤ S := by
    rw [hA]
    exact (Subgroup.closure_le _).2 fun x hx => hx.1
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (A : Set G) := by
    rw [hA]
    exact le_normalizer_closure_involutions _
  have hinv : ∀ x ∈ (S : Subgroup G), orderOf x = 2 → x ∈ A := fun x hx hx2 => by
    rw [hA]
    exact Subgroup.subset_closure ⟨hx, hx2⟩
  have h1 : ∀ s ∈ (S : Subgroup G), ∃ ℓ : Additive A →+ ZMod 2,
      ℓ (Additive.ofMul (⟨z, hzA⟩ : A)) = 0 ∧
        ∀ a : A, s * a * s⁻¹ = a * z ^ (ℓ (Additive.ofMul a)).val := by
    intro s hs
    have hmem : (fun a : A =>
        (⟨s * a * s⁻¹, (Subgroup.mem_normalizer_iff.1 (hSN hs) a).1 a.2⟩ : A)) ∈
        {f : A → A | ∃ s ∈ (S : Subgroup G), ∀ a : A, (f a : G) = s * a * s⁻¹} :=
      ⟨s, hs, fun a => rfl⟩
    rw [hshear] at hmem
    obtain ⟨ℓ, hℓz, hℓ⟩ := hmem
    exact ⟨ℓ, hℓz, fun a => hℓ a⟩
  have h2 : ∀ ℓ : Additive A →+ ZMod 2, ℓ (Additive.ofMul (⟨z, hzA⟩ : A)) = 0 →
      ∃ s ∈ (S : Subgroup G), ∀ a : A, s * a * s⁻¹ = a * z ^ (ℓ (Additive.ofMul a)).val := by
    intro ℓ hℓz
    have hmem : (fun a : A =>
        (⟨a * z ^ (ℓ (Additive.ofMul a)).val, A.mul_mem a.2 (A.pow_mem hzA _)⟩ : A)) ∈
        {f : A → A | ∃ ℓ : Additive A →+ ZMod 2, ℓ (Additive.ofMul (⟨z, hzA⟩ : A)) = 0 ∧
          ∀ a : A, (f a : G) = a * z ^ (ℓ (Additive.ofMul a)).val} :=
      ⟨ℓ, hℓz, fun a => rfl⟩
    rw [← hshear] at hmem
    obtain ⟨s, hs, hsf⟩ := hmem
    exact ⟨s, hs, fun a => (hsf a).symm⟩
  have hN : ∀ n ∈ Subgroup.normalizer (A : Set G), n * z * n⁻¹ = z := fun n hn =>
    normalizer_fixes_shear_axis S hSN hcomm hA2 (by rw [hA16]; norm_num) hzA hz1 h1 h2 hn
  refine ⟨⟨⟨z, hAS hzA⟩, Subgroup.mem_center_iff.2 fun s => Subtype.ext ?_, rfl⟩, ?_⟩
  · obtain ⟨ℓ, hℓz, hℓ⟩ := h1 s s.2
    have hsz := hℓ ⟨z, hzA⟩
    rw [hℓz, ZMod.val_zero, pow_zero, mul_one] at hsz
    exact mul_inv_eq_iff_eq_mul.1 hsz
  · ext x
    constructor
    · rintro ⟨⟨g, rfl⟩, hx⟩
      exact conj_mem_eq_of_normalizer_fixes S hinv hcomm hA2 hzA hz1 hN hx
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨⟨1, by group⟩, hAS hzA⟩

end CFSG.LocalAnalysis.ComponentInitial
