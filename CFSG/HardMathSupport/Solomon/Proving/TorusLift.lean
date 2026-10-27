module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsLift

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open Subgroup CFSG.HardMathSupport.Timmesfeld.LocalTwo

structure TorusData (ι : Type*) (p : ℕ) (S : Type*) [Group S] where
  X : ι → S
  Sw : ι → S
  comm : ∀ i j, Commute (X i) (X j)
  pow : ∀ i, X i ^ p = 1
  sw_self : ∀ k, Sw k * X k * (Sw k)⁻¹ = (X k)⁻¹
  sw_other : ∀ j k, j ≠ k → Sw k * X j * (Sw k)⁻¹ = (X k)⁻¹ * X j

section Main

variable {ι : Type*} {p : ℕ} {S : Type*} [Group S]

theorem TorusData.comm_W (D : TorusData ι p S) :
    ∀ a ∈ closure (Set.range D.X), ∀ b ∈ closure (Set.range D.X), Commute a b := by
  have h1 : ∀ i, ∀ b ∈ closure (Set.range D.X), Commute (D.X i) b := by
    intro i b hb
    induction hb using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact D.comm i j
    | one => exact Commute.one_right _
    | mul x y _ _ hx hy => exact hx.mul_right hy
    | inv x _ hx => exact hx.inv_right
  intro a ha b hb
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact h1 j b hb
  | one => exact Commute.one_left _
  | mul x y _ _ hx hy => exact hx.mul_left hy
  | inv x _ hx => exact hx.inv_left

theorem TorusData.swap_W (D : TorusData ι p S) (k : ι) :
    ∀ y ∈ closure (Set.range D.X), (D.Sw k * y * (D.Sw k)⁻¹ ∈ closure (Set.range D.X)) ∧
      y * (D.Sw k * y * (D.Sw k)⁻¹)⁻¹ ∈ zpowers (D.X k) := by
  classical
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases hjk : j = k
    · subst hjk
      rw [D.sw_self]
      refine ⟨inv_mem (subset_closure ⟨j, rfl⟩), ?_⟩
      rw [inv_inv]
      exact mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
    · rw [D.sw_other j k hjk]
      refine ⟨mul_mem (inv_mem (subset_closure ⟨k, rfl⟩)) (subset_closure ⟨j, rfl⟩), ?_⟩
      have : D.X j * ((D.X k)⁻¹ * D.X j)⁻¹ = D.X k := by group
      rw [this]
      exact Subgroup.mem_zpowers _
  | one => simp
  | mul x y hx hy ihx ihy =>
    obtain ⟨hx1, hx2⟩ := ihx
    obtain ⟨hy1, hy2⟩ := ihy
    have e : D.Sw k * (x * y) * (D.Sw k)⁻¹ =
        (D.Sw k * x * (D.Sw k)⁻¹) * (D.Sw k * y * (D.Sw k)⁻¹) := by group
    rw [e]
    refine ⟨mul_mem hx1 hy1, ?_⟩
    have hWc : ∀ a ∈ closure (Set.range D.X), ∀ b ∈ closure (Set.range D.X), a * b = b * a :=
      fun a ha b hb => (D.comm_W a ha b hb).eq
    have e2 : x * y * ((D.Sw k * x * (D.Sw k)⁻¹) * (D.Sw k * y * (D.Sw k)⁻¹))⁻¹ =
        (x * (D.Sw k * x * (D.Sw k)⁻¹)⁻¹) * (y * (D.Sw k * y * (D.Sw k)⁻¹)⁻¹) :=
      comm_aux_mul hWc hx hy hx1 hy1
    rw [e2]
    exact mul_mem hx2 hy2
  | inv x hx ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : D.Sw k * x⁻¹ * (D.Sw k)⁻¹ = (D.Sw k * x * (D.Sw k)⁻¹)⁻¹ := by group
    rw [e]
    refine ⟨inv_mem h1, ?_⟩
    rw [inv_inv]
    have hWc : ∀ a ∈ closure (Set.range D.X), ∀ b ∈ closure (Set.range D.X), a * b = b * a :=
      fun a ha b hb => (D.comm_W a ha b hb).eq
    have : x⁻¹ * (D.Sw k * x * (D.Sw k)⁻¹) = (x * (D.Sw k * x * (D.Sw k)⁻¹)⁻¹)⁻¹ :=
      comm_aux_inv hWc hx h1
    rw [this]
    exact inv_mem h2

theorem exists_cover_torus_core [Nonempty ι] (hp : p.Prime) {Lb : Type*} [Group Lb] [Finite Lb]
    (D : TorusData ι p S) (Γ : Lb →* S) (hΓ : Function.Surjective Γ)
    (hZ : Γ.ker ≤ Subgroup.center Lb) (hodd : Odd (Nat.card Γ.ker)) :
    ∃ E : Subgroup Lb, CFSG.Open.IsElemAbelian p E ∧ E ⊓ Γ.ker = ⊥ ∧
      E.map Γ = Subgroup.closure (Set.range D.X) ∧
      ∀ T : S, T ≠ 1 → (∃ e : ℕ, T ^ 2 ^ e = 1) → (∀ i, Commute T (D.X i)) →
        (∀ i, Commute T (D.Sw i)) →
        ∃ U : Subgroup Lb, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.centralizer (U : Set Lb) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨i0⟩ := ‹Nonempty ι›
  set Zk := Γ.ker with hZk
  have hc : ∀ z ∈ Zk, ∀ g : Lb, z * g = g * z := fun z hz g =>
    (Subgroup.mem_center_iff.1 (hZ hz) g).symm
  obtain ⟨m, hmN⟩ := hodd
  have hm : ∀ w ∈ Zk, w ^ (2 * m + 1) = 1 := by
    intro w hw
    have := pow_card_eq_one' (G := Zk) (x := ⟨w, hw⟩)
    rw [hmN] at this
    exact congrArg Subtype.val this
  have hodd2 : ∀ w ∈ Zk, w ^ 2 = 1 → w = 1 := by
    intro w hw h2
    calc w = w ^ (2 * m + 1) * w := by rw [hm w hw, one_mul]
      _ = w ^ (2 * m + 1 + 1) := (pow_succ w _).symm
      _ = (w ^ 2) ^ (m + 1) := by rw [← pow_mul]; congr 1
      _ = 1 := by rw [h2, one_pow]
  choose xh hxh using fun k => hΓ (D.X k)
  choose sh hsh using fun k => hΓ (D.Sw k)
  have hsu : ∀ k u, Γ u = D.X k → ∃ z ∈ Zk, sh k * u * (sh k)⁻¹ = u⁻¹ * z := by
    intro k u hu
    refine ⟨u * (sh k * u * (sh k)⁻¹), ?_, by group⟩
    rw [hZk, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hsh, hu, D.sw_self]
    exact mul_inv_cancel _
  set W := closure (Set.range D.X) with hW
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => (D.comm_W a ha b hb).eq
  set Wt : Subgroup Lb := W.comap Γ with hWt
  set R : Set Lb := {u | Γ u ∈ Set.range D.X} with hR
  have hRmem : ∀ k u, Γ u = D.X k → u ∈ R := fun k u hu => ⟨k, hu.symm⟩
  have hker_le : Zk ≤ closure R := by
    intro z hz
    have h1 : xh i0 * z ∈ R := by
      refine ⟨i0, ?_⟩
      rw [map_mul, hxh, (MonoidHom.mem_ker.1 hz), mul_one]
    have h2 : xh i0 ∈ R := hRmem i0 _ (hxh i0)
    have := mul_mem (subset_closure h1) (inv_mem (subset_closure h2))
    have e : xh i0 * z * (xh i0)⁻¹ = z := by
      calc xh i0 * z * (xh i0)⁻¹ = z * xh i0 * (xh i0)⁻¹ := by rw [← hc z hz (xh i0)]
        _ = z := by group
    rwa [e] at this
  have hWt_le : Wt ≤ closure R := by
    have h2 : (closure R).map Γ = W := by
      rw [MonoidHom.map_closure, hW]
      congr 1
      ext w
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro hw
        obtain ⟨u, rfl⟩ := hΓ w
        exact ⟨u, hw, rfl⟩
    calc Wt = W.comap Γ := rfl
      _ = ((closure R).map Γ).comap Γ := by rw [h2]
      _ = closure R ⊔ Γ.ker := Subgroup.comap_map_eq _ _
      _ = closure R := sup_eq_left.2 hker_le
      _ ≤ closure R := le_rfl
  have hXW : ∀ k, D.X k ∈ W := fun k => subset_closure ⟨k, rfl⟩
  have hA : ∀ k u, Γ u = D.X k → ∀ v ∈ Wt, u * v = v * u := by
    intro k u hu v hv
    obtain ⟨z, hz, hsu'⟩ := hsu k u hu
    have hvW : Γ v ∈ W := hv
    have hv'W : Γ (sh k * v * (sh k)⁻¹) ∈ W := by
      rw [map_mul, map_mul, map_inv, hsh]
      exact (D.swap_W k _ hvW).1
    have h1 : u * v * u⁻¹ * v⁻¹ ∈ Zk := by
      rw [hZk, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hu]
      rw [hWc _ (hXW k) _ hvW]
      group
    have h2 : u * (sh k * v * (sh k)⁻¹) * u⁻¹ * (sh k * v * (sh k)⁻¹)⁻¹ ∈ Zk := by
      rw [hZk, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hu]
      rw [hWc _ (hXW k) _ hv'W]
      group
    have h3 : u * (v * (sh k * v * (sh k)⁻¹)⁻¹) = (v * (sh k * v * (sh k)⁻¹)⁻¹) * u := by
      obtain ⟨i, hi⟩ := (D.swap_W k _ hvW).2
      have hi' : D.X k ^ i = Γ v * (D.Sw k * Γ v * (D.Sw k)⁻¹)⁻¹ := hi
      have hG : Γ (v * (sh k * v * (sh k)⁻¹)⁻¹) = Γ v * (D.Sw k * Γ v * (D.Sw k)⁻¹)⁻¹ := by
        simp [hsh]
      have hz'' : (u ^ i)⁻¹ * (v * (sh k * v * (sh k)⁻¹)⁻¹) ∈ Zk := by
        rw [hZk, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hu, hG, hi']
        group
      set z'' := (u ^ i)⁻¹ * (v * (sh k * v * (sh k)⁻¹)⁻¹) with hz''def
      have e : v * (sh k * v * (sh k)⁻¹)⁻¹ = u ^ i * z'' := by rw [hz''def]; group
      rw [e]
      have hu1 : Commute u (u ^ i) := Commute.self_zpow u i
      have hu2 : Commute u z'' := (hc z'' hz'' u).symm
      exact (hu1.mul_right hu2).eq
    have := pairing_eq_one hc hodd2 hz hsu' h1 h2 h3
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  have hWtcomm : ∀ a ∈ Wt, ∀ b ∈ Wt, a * b = b * a := by
    have h1 : closure R ≤ Subgroup.centralizer (Wt : Set Lb) := by
      rw [Subgroup.closure_le]
      intro u hu
      obtain ⟨k, hk⟩ := hu
      exact Subgroup.mem_centralizer_iff.2 fun v hv => (hA k u hk.symm v hv).symm
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.1 (h1 (hWt_le ha)) b hb).symm
  let Ω : Subgroup Lb :=
    { carrier := {y | y ∈ Wt ∧ y ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [(show Commute a b from hWtcomm a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow _⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hlift : ∀ k, ∃ y ∈ Ω, Γ y = D.X k := by
    intro k
    obtain ⟨z, hz, hsz⟩ := hsu k (xh k) (hxh k)
    have hup : (xh k) ^ p ∈ Zk := by
      rw [hZk, MonoidHom.mem_ker, map_pow, hxh, D.pow]
    obtain ⟨g, hg, hgp⟩ := exists_lift_pow_eq_one hc hm hz hsz hup
    have hgΓ : Γ g = 1 := by rw [hZk] at hg; exact MonoidHom.mem_ker.1 hg
    have hΓy : Γ (xh k * g⁻¹) = D.X k := by rw [map_mul, map_inv, hgΓ, hxh, inv_one, mul_one]
    exact ⟨xh k * g⁻¹, ⟨by rw [hWt]; exact (Subgroup.mem_comap.2 (by rw [hΓy]; exact hXW k)), hgp⟩,
      hΓy⟩
  have hΩW : Ω.map Γ = W := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.1
    · rw [hW, Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨y, hy, hyk⟩ := hlift k
      exact ⟨y, hy, hyk⟩
  obtain ⟨E, hEΩ, hEZ, hEcover⟩ := exists_sub_complement hp Ω Zk
    (fun a ha b hb => hWtcomm a ha.1 b hb.1) (fun a ha => ha.2)
  have hEmap : E.map Γ = W := by
    refine le_antisymm ?_ ?_
    · rw [← hΩW]
      exact Subgroup.map_mono hEΩ
    · intro w hw
      rw [← hΩW] at hw
      obtain ⟨g, hg, rfl⟩ := hw
      obtain ⟨e, he, z, hz, rfl⟩ := hEcover g hg
      have hzΓ : Γ z = 1 := by rw [hZk] at hz; exact MonoidHom.mem_ker.1 hz
      refine ⟨e, he, ?_⟩
      rw [map_mul, hzΓ, mul_one]
  have hEel : CFSG.Open.IsElemAbelian p E :=
    ⟨⟨⟨fun a b => Subtype.ext (hWtcomm a (hEΩ a.2).1 b (hEΩ b.2).1)⟩⟩, fun x hx => (hEΩ hx).2⟩
  refine ⟨E, hEel, hEZ, hEmap, ?_⟩
  intro T hT1 hT2 hTX hTS
  obtain ⟨u0, hu0⟩ := hΓ T
  obtain ⟨e2, he2⟩ := hT2
  have hcop : Nat.Coprime (2 * m + 1) (orderOf T) := by
    have h1 : Nat.Coprime (2 * m + 1) (2 ^ e2) :=
      Nat.Coprime.pow_right _ (Odd.coprime_two_right ⟨m, rfl⟩)
    exact h1.coprime_dvd_right (orderOf_dvd_of_pow_eq_one he2)
  obtain ⟨c, hcT⟩ := exists_pow_eq_self_of_coprime hcop
  set that : Lb := u0 ^ ((2 * m + 1) * c) with hthat
  have hΓt : Γ that = T := by rw [hthat, map_pow, hu0, pow_mul, hcT]
  have hthat2 : that ^ (2 ^ e2) = 1 := by
    have h1 : u0 ^ (2 ^ e2) ∈ Zk := by
      rw [hZk, MonoidHom.mem_ker, map_pow, hu0, he2]
    calc that ^ (2 ^ e2) = u0 ^ ((2 * m + 1) * c * 2 ^ e2) := by rw [hthat, ← pow_mul]
      _ = (u0 ^ (2 ^ e2)) ^ ((2 * m + 1) * c) := by rw [← pow_mul]; congr 1; ring
      _ = ((u0 ^ (2 ^ e2)) ^ (2 * m + 1)) ^ c := by rw [pow_mul]
      _ = 1 := by rw [hm _ h1, one_pow]
  have hthat1 : that ≠ 1 := fun h => hT1 (by rw [← hΓt, h, map_one])
  have hC : ∀ k u, Γ u = D.X k → u * that = that * u := by
    intro k u hu
    obtain ⟨z, hz, hsu'⟩ := hsu k u hu
    have e : (D.Sw k)⁻¹ * T * D.Sw k = T := by
      rw [mul_assoc, (hTS k).eq, inv_mul_cancel_left]
    have hz' : that⁻¹ * ((sh k)⁻¹ * that * sh k) ∈ Zk := by
      rw [hZk, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hsh, hΓt, e]
      exact inv_mul_cancel _
    have hst : (sh k)⁻¹ * that * sh k = that * (that⁻¹ * ((sh k)⁻¹ * that * sh k)) := by group
    have hut : u * that * u⁻¹ * that⁻¹ ∈ Zk := by
      rw [hZk, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hu, hΓt,
        ← (hTX k).eq]
      group
    have := commutator_t_eq_one hc hodd2 hz hz' hsu' hst hut
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  have hCt : ∀ a ∈ Wt, a * that = that * a := by
    have h1 : closure R ≤ Subgroup.centralizer ({that} : Set Lb) := by
      rw [Subgroup.closure_le]
      intro u hu
      obtain ⟨k, hk⟩ := hu
      exact Subgroup.mem_centralizer_iff.2 fun v hv => by
        rw [Set.mem_singleton_iff.1 hv]
        exact (hC k u hk.symm).symm
    intro a ha
    exact (Subgroup.mem_centralizer_iff.1 (h1 (hWt_le ha)) that rfl).symm
  refine ⟨Subgroup.zpowers that, ?_, ?_, ?_⟩
  · exact fun h => hthat1 (Subgroup.zpowers_eq_bot.1 h)
  · have hord : orderOf that ∣ 2 ^ e2 := orderOf_dvd_of_pow_eq_one hthat2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  · intro x hx
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hx' : x ∈ Wt := (hEΩ hx).1
    have hcm : Commute that x := (hCt x hx').symm
    exact (hcm.zpow_left i).eq

theorem exists_cover_torus [Finite ι] [Nonempty ι] (hp : p.Prime)
    {Lb : Type*} [Group Lb] [Finite Lb] (D : TorusData ι p S) (Γ : Lb →* S)
    (hΓ : Function.Surjective Γ) (hZ : Γ.ker ≤ Subgroup.center Lb)
    (hodd : Odd (Nat.card Γ.ker)) :
    ∃ E : Subgroup Lb, CFSG.Open.IsElemAbelian p E ∧ E ⊓ Γ.ker = ⊥ ∧
      E.map Γ = Subgroup.closure (Set.range D.X) := by
  obtain ⟨E, h1, h2, h3, -⟩ := exists_cover_torus_core hp D Γ hΓ hZ hodd
  exact ⟨E, h1, h2, h3⟩

theorem exists_cover_torus_two [Finite ι] [Nonempty ι] (hp : p.Prime)
    {Lb : Type*} [Group Lb] [Finite Lb] (D : TorusData ι p S) (Γ : Lb →* S)
    (hΓ : Function.Surjective Γ) (hZ : Γ.ker ≤ Subgroup.center Lb)
    (hodd : Odd (Nat.card Γ.ker)) {T : S} (hT1 : T ≠ 1) (hT2 : ∃ e : ℕ, T ^ 2 ^ e = 1)
    (hTX : ∀ i, Commute T (D.X i)) (hTS : ∀ i, Commute T (D.Sw i)) :
    ∃ E U : Subgroup Lb, CFSG.Open.IsElemAbelian p E ∧ E ⊓ Γ.ker = ⊥ ∧
      E.map Γ = Subgroup.closure (Set.range D.X) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.centralizer (U : Set Lb) := by
  obtain ⟨E, h1, h2, h3, h4⟩ := exists_cover_torus_core hp D Γ hΓ hZ hodd
  obtain ⟨U, hU1, hU2, hU3⟩ := h4 T hT1 hT2 hTX hTS
  exact ⟨E, U, h1, h2, h3, hU1, hU2, hU3⟩

end Main

end CFSG.HardMathSupport.Solomon.Proving
