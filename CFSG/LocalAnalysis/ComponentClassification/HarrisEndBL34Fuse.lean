module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Cent
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34T1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34X
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndLift

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

theorem EndB.card_centralizer_inner {s : Equiv.Perm (Fin 42)}
    (hs : s ∈ PSL3Four.S) (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    Nat.card ↥(centralizer {s} ⊓ PSL3Four.S) = 64 := by
  set x : PSL3Four.R := ⟨s, PSL3Four.S_le_R hs⟩ with hx
  have hx2 : orderOf x = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (Subtype.ext ?_) (fun h => hs1 (congrArg Subtype.val h))
    rw [Subgroup.coe_pow, Subgroup.coe_one, sq]
    exact hs2
  rcases (PSL3Four.orderOf_eq_two_iff x).mp hx2 with h | h | h | h
  · obtain ⟨c, hc, he⟩ := PSL3Four.eq_conj_of_isConj h
    rw [EndB.card_centralizer_conj_S hc he]
    exact PSL3Four.card_C₁
  · exact absurd hs (PSL3Four.not_mem_S_of_isConj h PSL3Four.not_mem_S_r₂)
  · exact absurd hs (PSL3Four.not_mem_S_of_isConj h PSL3Four.not_mem_S_r₃)
  · exact absurd hs (PSL3Four.not_mem_S_of_isConj h PSL3Four.not_mem_S_r₄)

theorem EndB.eq_one_or_eq_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G] {a b : G}
    (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) (ha2 : a ^ 2 = 1) : a = 1 ∨ a = b := by
  classical
  have : Fintype G := Fintype.ofFinite G
  by_contra h
  rw [not_or] at h
  obtain ⟨ha1, hab⟩ := h
  have hle := IsCyclic.card_pow_eq_one_le (α := G) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset G) ⊆ Finset.univ.filter (fun x : G => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact ha2
    · exact hb2
  have hcard : ({1, a, b} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hab
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hb1⟩
  have := Finset.card_le_card hsub
  omega

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.LLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S}

theorem false_of_card_gt (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥) (g : X)
    (hτM : g * t * g⁻¹ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    {U : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}
    (hU : U ≤ centralizer {(QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}) (hU2 : IsPGroup 2 U)
    (h128 : 128 < Nat.card U) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hτ2 : (g * t * g⁻¹) ^ 2 = 1 := by
    rw [sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ← sq, ht2]
    group
  obtain ⟨Ŝ, hŜ⟩ := exists_isSylowOf 2 (centralizer ({g * t * g⁻¹} : Set X) ⊓
    centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
  have hŜbar := isSylowOf_barOf_centralizer hτM hτ2 hŜ
  have hŜM : Ŝ ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    hŜ.le.trans inf_le_right
  have hcard : Nat.card U ≤ Nat.card Ŝ := by
    rw [← card_barOf hŜM hŜ.isPGroup, hŜbar.card_eq]
    exact card_le_twoPart hU2 hU
  have hŜ'H : Ŝ.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨s, hs', rfl⟩
    have hsτ : s * (g * t * g⁻¹) = (g * t * g⁻¹) * s :=
      mem_centralizer_singleton_iff.mp (hŜ.le hs').1
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * s * g * t = g⁻¹ * (s * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * s) * g := by rw [hsτ]
      _ = t * (g⁻¹ * s * g) := by group
  have hle := card_le_twoPart (hŜ.isPGroup.map _) hŜ'H
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at hle
  have hS := hs.sylow.card_eq
  rw [twoPart] at hle
  have := hL.card_S_le hZ
  omega

theorem card_comap_pi (hL : LLayer hs π) (Ys : Subgroup ↥PSL3Four.S) :
    Nat.card ↥(Ys.comap π) = Nat.card ↥π.ker * Nat.card ↥Ys := by
  have hcardE := Subgroup.card_ker_mul_card_range π
  rw [MonoidHom.range_eq_top.mpr hL.surj, card_top] at hcardE
  have hYidx : (Ys.comap π).index = Ys.index := Subgroup.index_comap_of_surjective Ys hL.surj
  have h1 := Subgroup.card_mul_index (Ys.comap π)
  have h2 := Subgroup.card_mul_index Ys
  have hpos : 0 < Ys.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [hYidx] at h1
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, mul_assoc (Nat.card π.ker), h2, hcardE]

theorem card_centralizer_z (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (hQc : IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    (hzM : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) :
    IsPGroup 2 ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {(QuotientGroup.mk ⟨z, hzM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}) ∧
      64 ≤ Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {(QuotientGroup.mk ⟨z, hzM⟩ :
          MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzK : z ∈ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := hs.lemma45.z_mem.2
  have hzKb : (QuotientGroup.mk ⟨z, hzM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := ⟨⟨z, hzM⟩, hzK, rfl⟩
  have hzE := hs.KBar_le_layer hzKb
  set z' : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := ⟨_, hzE⟩ with hz'
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hz'2 : z' * z' = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hz', ← QuotientGroup.mk_mul, Subgroup.coe_one]
    have : (⟨z, hzM⟩ : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) *
        ⟨z, hzM⟩ = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← sq, hz2, Subgroup.coe_one])
    rw [this, QuotientGroup.mk_one]
  have hπz1 : π z' ≠ 1 := by
    intro h
    have h1 : z' = 1 := hL.pi_injOn_KBar (a := z') (b := 1) hzKb (one_mem _) (by rw [h, map_one])
    have h2 := mk_injOn (zpowers_le.mpr hzM) (isPGroup_zpowers_of_sq hz2) (mem_zpowers z)
      (one_mem _) (congrArg Subtype.val h1)
    have := hs.setup.z_order
    rw [h2, orderOf_one] at this
    norm_num at this
  set s : Equiv.Perm (Fin 42) := ((π z' : PSL3Four.S) : Equiv.Perm (Fin 42)) with hsdef
  have hs2 : s * s = 1 := by
    rw [hsdef, ← Subgroup.coe_mul, ← map_mul, hz'2, map_one, Subgroup.coe_one]
  have hs1 : s ≠ 1 := fun h => hπz1 (Subtype.ext h)
  have h64 := EndB.card_centralizer_inner (π z').2 hs2 hs1
  set Ys : Subgroup ↥PSL3Four.S := (centralizer {s}).comap PSL3Four.S.subtype with hYs
  have hYs64 : Nat.card Ys = 64 := by
    rw [hYs, ← Subgroup.subgroupOf, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, h64]
  set Y := Ys.comap π with hY
  have hYcard : Nat.card Y = Nat.card π.ker * 64 := by rw [hY, hL.card_comap_pi Ys, hYs64]
  have hz'Y : z' ∈ Y := by
    rw [hY, mem_comap, hYs, mem_comap]
    exact mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨b, hb, hbeq⟩ := hL.h412.lemma46c.2.2 hZ
  have hbQ : (b : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := hL.center_le_pCore ⟨b, hb, rfl⟩
  have horb : {y : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) |
      ∃ a ∈ Y, a * z' * a⁻¹ = y} ⊆ {z', z' * b} := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' : π a * π z' = π z' * π a := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact mem_centralizer_singleton_iff.mp ha
    have hc : (a * z' * a⁻¹) * z'⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ha']
      group
    rw [hL.ker] at hc
    set c := (a * z' * a⁻¹) * z'⁻¹ with hcdef
    have hcz : a * z' * a⁻¹ = c * z' := by rw [hcdef]; group
    have hc2 : c ^ 2 = 1 := by
      have h1 : (a * z' * a⁻¹) * (a * z' * a⁻¹) = 1 := by
        rw [show a * z' * a⁻¹ * (a * z' * a⁻¹) = a * (z' * z') * a⁻¹ by group, hz'2]
        group
      have hcomm : z' * c = c * z' := mem_center_iff.mp hc z'
      have h3 : c * z' * (c * z') = c * c * (z' * z') := by
        rw [show c * z' * (c * z') = c * (z' * c) * z' by group, hcomm]
        group
      rw [hcz, h3, hz'2, mul_one] at h1
      rw [sq]
      exact h1
    have hcQ : (c : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
        pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := hL.center_le_pCore ⟨c, hc, rfl⟩
    have hβ2 := hs.betaBar_sq
    have hβ1 := hs.betaBar_ne_one
    have hbeq' : (b : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
        betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) := hbeq
    have hbQ2 : (⟨b, hbQ⟩ : ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ^ 2 = 1 := by
      apply Subtype.ext
      change (b : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ^ 2 = 1
      rw [hbeq', hβ2]
    have hbQ1 : (⟨b, hbQ⟩ : ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ≠ 1 := by
      intro h
      apply hβ1
      rw [← hbeq']
      exact congrArg Subtype.val h
    have hcQ2 : (⟨c, hcQ⟩ : ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ^ 2 = 1 := by
      apply Subtype.ext
      change (c : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ^ 2 = 1
      rw [← Subgroup.coe_pow, hc2, Subgroup.coe_one]
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases EndB.eq_one_or_eq_of_isCyclic hbQ2 hbQ1 hcQ2 with h | h
    · left
      have : c = 1 := Subtype.ext (by
        have := congrArg Subtype.val h
        simpa using this)
      rw [hcz, this, one_mul]
    · right
      have h' := congrArg Subtype.val h
      have : c = b := Subtype.ext h'
      rw [hcz, this]
      exact (mem_center_iff.mp hb z').symm
  have hncard : (centralizer {z'}).relIndex Y ≤ 2 := by
    rw [← ncard_conj_orbit Y hz'Y]
    calc _ ≤ ({z', z' * b} : Set _).ncard := Set.ncard_le_ncard horb (Set.toFinite _)
      _ ≤ ({z' * b} : Set _).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have hrel := Subgroup.relIndex_mul_card (centralizer {z'}) Y
  have hker2 : 2 ≤ Nat.card π.ker := by
    rw [hL.ker]
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ
  have hCY : Nat.card ↥(centralizer {z'} ⊓ Y) ≤ Nat.card ↥(centralizer ({z'} : Set _)) :=
    Subgroup.card_le_of_le inf_le_left
  have hC64 : 64 ≤ Nat.card ↥(centralizer ({z'} : Set _)) := by
    have : Nat.card Y ≤ 2 * Nat.card ↥(centralizer {z'} ⊓ Y) := by
      rw [← hrel]
      exact Nat.mul_le_mul_right _ hncard
    omega
  have hCle : centralizer ({z'} : Set _) ≤ Y := by
    intro e he
    rw [hY, mem_comap, hYs, mem_comap, mem_centralizer_singleton_iff, Subgroup.coe_subtype,
      ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp he]
  have hY2 : IsPGroup 2 Y := by
    refine IsPGroup.comap_of_ker_isPGroup (IsPGroup.of_card (n := 6) (by rw [hYs64]; norm_num))
      π ?_
    rw [hL.ker]
    exact hL.isPGroup_center
  have heq : (centralizer {(QuotientGroup.mk ⟨z, hzM⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}).subgroupOf
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = centralizer {z'} := by
    ext e
    rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
      Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]
  have hcard : Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {(QuotientGroup.mk ⟨z, hzM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}) =
      Nat.card ↥(centralizer ({z'} : Set _)) := by
    rw [← heq, ← Subgroup.inf_subgroupOf_left]
    exact (Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  refine ⟨?_, by rw [hcard]; exact hC64⟩
  have h2 : IsPGroup 2 ↥(centralizer ({z'} : Set _)) := hY2.to_le hCle
  refine h2.of_equiv ?_
  rw [← heq, ← Subgroup.inf_subgroupOf_left]
  exact (subgroupOfEquivOfLe inf_le_left)

omit [Finite X] in
theorem _root_.CFSG.ComponentClassification.HarrisLit.EndB.mk_comm {M : Subgroup X} {a b : X}
    (ha : a ∈ M) (hb : b ∈ M) (hab : a * b = b * a) :
    (QuotientGroup.mk ⟨a, ha⟩ : ↥M ⧸ pPrimeCore 2 ↥M) * QuotientGroup.mk ⟨b, hb⟩ =
      QuotientGroup.mk ⟨b, hb⟩ * QuotientGroup.mk ⟨a, ha⟩ := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext hab

omit [Finite X] in
theorem _root_.CFSG.ComponentClassification.HarrisLit.EndB.mk_sq {M : Subgroup X} {a : X}
    (ha : a ∈ M) (ha2 : a ^ 2 = 1) :
    (QuotientGroup.mk ⟨a, ha⟩ : ↥M ⧸ pPrimeCore 2 ↥M) ^ 2 = 1 := by
  rw [← QuotientGroup.mk_pow]
  have : (⟨a, ha⟩ : ↥M) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, ha2, Subgroup.coe_one])
  rw [this, QuotientGroup.mk_one]

theorem exists_card_ge_256 (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (hQc : IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    (hzM : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) :
    ∃ U : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      U ≤ centralizer {(QuotientGroup.mk ⟨z, hzM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} ∧
      IsPGroup 2 U ∧ 256 ≤ Nat.card U := by
  obtain ⟨x, hxD, hx2, hxM, h0, h1⟩ := hL.exists_x hZ
  obtain ⟨hA2, hA64⟩ := hL.card_centralizer_z hZ hQc hzM
  have htM := hs.setup.t_mem_centralizer_beta i j
  have htS : t ∈ S := hs.setup.T_le (mem_sup_left (mem_sup_left (mem_zpowers t)))
  have hxz : x * z = z * x := hs.setup.z_comm (mem_inf.mp hxD).1
  have htz : t * z = z * t := hs.setup.z_comm htS
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp
    (hs.standing.config.le_centralizer (mem_inf.mp hxD).2)
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have htb : hs.setup.tBar i j = (QuotientGroup.mk ⟨t, htM⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := rfl
  obtain ⟨hrt2, hrtS⟩ := hL.rho_t_facts
  obtain ⟨U, hU, hU2, hcard⟩ := hL.exists_card_ge_four_mul (le_inf inf_le_right
    (inf_le_left.trans le_sup_left)) hA2
    (a := QuotientGroup.mk ⟨x, hxM⟩) (b := QuotientGroup.mk ⟨t, htM⟩)
    (mem_centralizer_singleton_iff.mpr (EndB.mk_comm hxM hzM hxz))
    (mem_centralizer_singleton_iff.mpr (EndB.mk_comm htM hzM htz))
    (EndB.mk_sq hxM hx2) (EndB.mk_sq htM ht2) (EndB.mk_comm hxM htM hxt)
    (fun h => h0 ((hL.rho_mem_S_iff _).mpr h))
    (fun h => hrtS ((hL.rho_mem_S_iff _).mpr h))
    (fun h => h1 ((hL.rho_mem_S_iff _).mpr h))
  exact ⟨U, hU, hU2, by omega⟩

theorem false_of_conj_inner
    (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (hQc : IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) (g : X)
    (hτM : g * t * g⁻¹ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    (hτE : (QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzK : z ∈ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := hs.lemma45.z_mem.2
  have hzM : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    K_le_centralizer_beta i j hzK
  obtain ⟨U, hU, hU2, h256⟩ := hL.exists_card_ge_256 hZ hQc hzM
  set τb := (QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    with hτb
  set zb := (QuotientGroup.mk ⟨z, hzM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) with hzb
  suffices h : ∃ f u : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j), τb = f * u * f⁻¹ ∧
      centralizer {zb} ≤ centralizer {u} by
    obtain ⟨f, u, hfu, hCu⟩ := h
    refine hL.false_of_card_gt hZ g hτM (U := U.map (MulAut.conj f).toMonoidHom) ?_
      (hU2.map _) ?_
    · rintro _ ⟨y, hy, rfl⟩
      have hyu : y * u = u * y := mem_centralizer_singleton_iff.mp (hCu (hU hy))
      rw [mem_centralizer_singleton_iff, ← hτb, hfu]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc f * y * f⁻¹ * (f * u * f⁻¹) = f * (y * u) * f⁻¹ := by group
        _ = f * (u * y) * f⁻¹ := by rw [hyu]
        _ = f * u * f⁻¹ * (f * y * f⁻¹) := by group
    · rw [Subgroup.card_map_of_injective (MulAut.conj f).injective]
      omega
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hτ2' : (g * t * g⁻¹) ^ 2 = 1 := by
    rw [sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ← sq, ht2]
    group
  have hτ2 : τb ^ 2 = 1 := EndB.mk_sq hτM hτ2'
  have hτ1 : τb ≠ 1 := by
    intro h
    have h2 := mk_injOn (zpowers_le.mpr hτM) (isPGroup_zpowers_of_sq hτ2') (mem_zpowers _)
      (one_mem _) (by rw [← hτb, h]; rfl)
    have : g * t * g⁻¹ = 1 → t = 1 := fun h' => by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h']; group
    have ht1 : t ≠ 1 := by
      intro h'
      have := hs.standing.config.orderOf_eq
      rw [h', orderOf_one] at this
      norm_num at this
    exact ht1 (this h2)
  have hQE : ∀ q ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      ∀ e ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), e * q = q * e := by
    intro q hq e he
    rw [← hs.centralizer_layer_eq hL.h412] at hq
    exact mem_centralizer_iff.mp hq e he
  have hβc : ∀ y : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      y * betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
        betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * y :=
    fun y => mem_center_iff.mp (betaBar_mem_center _) y
  have hβQ := hs.betaBar_mem_pCore
  have hinvQ : ∀ q ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), q ^ 2 = 1 →
      q = 1 ∨ q = betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
    intro q hq hq2
    have hb2 : (⟨_, hβQ⟩ : ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, hs.betaBar_sq, Subgroup.coe_one])
    have hb1 : (⟨_, hβQ⟩ : ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ≠ 1 :=
      fun h => hs.betaBar_ne_one (congrArg Subtype.val h)
    rcases EndB.eq_one_or_eq_of_isCyclic hb2 hb1 (a := ⟨q, hq⟩)
      (Subtype.ext (by rw [Subgroup.coe_pow, hq2, Subgroup.coe_one])) with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have hρS := (hL.rho_mem_S_iff τb).mpr hτE
  obtain ⟨e, he⟩ := hL.surj ⟨_, hρS⟩
  have hρe := hL.rho_of_mem e
  rw [he] at hρe
  have hq : τb * (e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))⁻¹ ∈
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [← hL.rho_eq_one_iff]
    apply Subtype.ext
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hρe, Subgroup.coe_one]
    exact mul_inv_cancel _
  set q := τb * (e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))⁻¹ with hqdef
  have hτqe : τb = q * e := by rw [hqdef]; group
  by_cases he1 : π e = 1
  ·
    have heZ : e ∈ center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
      rw [← hL.ker]
      exact he1
    have heQ := hL.center_le_pCore ⟨e, heZ, rfl⟩
    have hτQ : τb ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
      rw [hτqe]
      exact mul_mem hq heQ
    rcases hinvQ τb hτQ hτ2 with h | h
    · exact absurd h hτ1
    · refine ⟨1, betaBar _, by rw [h]; group, fun y _ => ?_⟩
      exact mem_centralizer_singleton_iff.mpr (hβc y)
  ·
    have hzKb : zb ∈ KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := ⟨⟨z, hzM⟩, hzK, rfl⟩
    have hzE := hs.KBar_le_layer hzKb
    set z' : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := ⟨zb, hzE⟩ with hz'
    have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
    have hzb2 : zb * zb = 1 := by rw [← sq]; exact EndB.mk_sq hzM hz2
    have hz'2 : z' * z' = 1 := Subtype.ext (by rw [Subgroup.coe_mul]; exact hzb2)
    have hπz1 : π z' ≠ 1 := by
      intro h
      have h1 : z' = 1 := hL.pi_injOn_KBar (a := z') (b := 1) hzKb (one_mem _) (by rw [h, map_one])
      have h2 := mk_injOn (zpowers_le.mpr hzM) (isPGroup_zpowers_of_sq hz2) (mem_zpowers z)
        (one_mem _) (congrArg Subtype.val h1)
      have := hs.setup.z_order
      rw [h2, orderOf_one] at this
      norm_num at this
    have hπe2 : ((π e : PSL3Four.S) : Equiv.Perm (Fin 42)) * π e = 1 := by
      rw [he]
      change ((hL.rho τb : PSL3Four.R) : Equiv.Perm (Fin 42)) * (hL.rho τb : PSL3Four.R) = 1
      rw [← Subgroup.coe_mul, ← map_mul, ← sq, hτ2, map_one, Subgroup.coe_one]
    have hπz2 : ((π z' : PSL3Four.S) : Equiv.Perm (Fin 42)) * π z' = 1 := by
      rw [← Subgroup.coe_mul, ← map_mul, hz'2, map_one, Subgroup.coe_one]
    have hπe1 : ((π e : PSL3Four.S) : Equiv.Perm (Fin 42)) ≠ 1 := fun h => he1 (Subtype.ext h)
    have hπz1' : ((π z' : PSL3Four.S) : Equiv.Perm (Fin 42)) ≠ 1 :=
      fun h => hπz1 (Subtype.ext h)
    obtain ⟨y, hyS, hy⟩ := CatFactsL4U4.conj_of_mul_mem_S (PSL3Four.S_le_R (π z').2)
      (PSL3Four.S_le_R (π e).2) hπz2 hπe2 hπz1' hπe1 (mul_mem (inv_mem (π z').2) (π e).2)
    obtain ⟨f, hf⟩ := hL.surj ⟨y, hyS⟩
    have hc : (f * z' * f⁻¹)⁻¹ * e ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      simp only [map_mul, map_inv, hf, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
      rw [hy]
      exact inv_mul_cancel _
    rw [hL.ker] at hc
    set c := (f * z' * f⁻¹)⁻¹ * e with hcdef
    have hcQ := hL.center_le_pCore ⟨c, hc, rfl⟩
    have hec : e = f * z' * f⁻¹ * c := by rw [hcdef]; group
    have hqf : q * (f : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = f * q :=
      (hQE q hq f f.2).symm
    have hcf : (f : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))⁻¹ * (c : MBar (w ^ (orderOf w / 2) *
        t ^ i * z ^ j)) = c * (f : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))⁻¹ := by
      have := congrArg Subtype.val (mem_center_iff.mp hc f⁻¹)
      simpa using this
    have hczb : zb * (c : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = c * zb := by
      have := congrArg Subtype.val (mem_center_iff.mp hc z')
      simpa using this
    set fb : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) := (f : MBar (w ^ (orderOf w / 2) *
      t ^ i * z ^ j)) with hfb
    set cb : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) := (c : MBar (w ^ (orderOf w / 2) *
      t ^ i * z ^ j)) with hcb
    set u : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) := q * cb * zb with hu
    have hτu : τb = fb * u * fb⁻¹ := by
      calc τb = q * (fb * zb * fb⁻¹ * cb) := by
            rw [hτqe, hec]
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            rfl
        _ = (q * fb) * zb * (fb⁻¹ * cb) := by group
        _ = (fb * q) * zb * (cb * fb⁻¹) := by rw [hqf, hcf]
        _ = fb * q * (zb * cb) * fb⁻¹ := by group
        _ = fb * q * (cb * zb) * fb⁻¹ := by rw [hczb]
        _ = fb * u * fb⁻¹ := by rw [hu]; group
    have hqc : q * cb ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := mul_mem hq hcQ
    have hqc2 : (q * cb) ^ 2 = 1 := by
      have hu2 : u * u = 1 := by
        have : u = fb⁻¹ * τb * fb := by rw [hτu]; group
        rw [this, show fb⁻¹ * τb * fb * (fb⁻¹ * τb * fb) = fb⁻¹ * (τb * τb) * fb by group, ← sq,
          hτ2]
        group
      have hcomm := hQE _ hqc zb hzE
      rw [hu, show q * cb * zb * (q * cb * zb) = q * cb * (zb * (q * cb)) * zb by group, hcomm,
        show q * cb * (q * cb * zb) * zb = q * cb * (q * cb) * (zb * zb) by group, hzb2,
        mul_one] at hu2
      rw [sq]
      exact hu2
    rcases hinvQ _ hqc hqc2 with h | h
    · refine ⟨fb, u, hτu, ?_⟩
      rw [hu, h, one_mul]
    · refine ⟨fb, u, hτu, fun y hy => ?_⟩
      rw [hu, h, mem_centralizer_singleton_iff]
      have hyz := mem_centralizer_singleton_iff.mp hy
      set bb := betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) with hbb
      calc y * (bb * zb) = (y * bb) * zb := (mul_assoc y bb zb).symm
        _ = (bb * y) * zb := by rw [hβc y]
        _ = bb * (y * zb) := mul_assoc bb y zb
        _ = bb * (zb * y) := by rw [hyz]
        _ = bb * zb * y := (mul_assoc bb zb y).symm

theorem card_le_32_of_unitary_X
    (hUC : GrSLit.L34UnitaryCentralizerFact) (hL : LLayer hs π)
    (hQE : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) {τ : X}
    (hτM : τ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) (hτ2 : τ ^ 2 = 1)
    {c : Equiv.Perm (Fin 42)} (hc : c ∈ PSL3Four.R)
    (hτc : ((hL.rho (QuotientGroup.mk ⟨τ, hτM⟩) : PSL3Four.R) : Equiv.Perm (Fin 42)) =
      c * PSL3Four.r₄ * c⁻¹) {R : Subgroup X}
    (hR : R ≤ centralizer ({τ} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})
    (hR2 : IsPGroup 2 R) : Nat.card R ≤ 32 := by
  have hRM : R ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    hR.trans inf_le_right
  rw [← card_barOf hRM hR2]
  refine hL.card_le_32_of_unitary hUC hQE (EndB.mk_sq hτM hτ2) hc hτc ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact EndB.mk_comm _ _ (mem_centralizer_singleton_iff.mp (mem_inf.mp (hR hr)).1)
  · have hR2' : IsPGroup 2 ↥(R.subgroupOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} :
        Set X))) := hR2.of_equiv (subgroupOfEquivOfLe hRM).symm
    exact hR2'.map _

theorem false_of_conj_unitary
    (hKF : AutPSL2FusionInput) (hUC : GrSLit.L34UnitaryCentralizerFact) (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (hQE : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (g : X)
    (hτM : g * t * g⁻¹ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    {c : Equiv.Perm (Fin 42)} (hc : c ∈ PSL3Four.R)
    (hτc : ((hL.rho (QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩) : PSL3Four.R) :
      Equiv.Perm (Fin 42)) = c * PSL3Four.r₄ * c⁻¹)
    {a b : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)}
    (ha : a ∈ centralizer {(QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))})
    (hb : b ∈ centralizer {(QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))})
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (hab : a * b = b * a)
    (haE : a ∉ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (hbE : b ∉ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (habE : a * b ∉ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hτ2 : (g * t * g⁻¹) ^ 2 = 1 := by
    rw [sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ← sq, ht2]
    group
  obtain ⟨Ŝ, hŜ⟩ := exists_isSylowOf 2 (centralizer ({g * t * g⁻¹} : Set X) ⊓
    centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
  have hŜbar := isSylowOf_barOf_centralizer hτM hτ2 hŜ
  have hŜM : Ŝ ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    hŜ.le.trans inf_le_right
  have hle := hL.card_le_32_of_unitary_X hUC hQE hτM hτ2 hc hτc hŜ.le hŜ.isPGroup
  obtain ⟨U, hU, hU2, h32⟩ := hL.exists_card_ge_32 hUC (EndB.mk_sq hτM hτ2) hc hτc ha hb ha2 hb2
    hab haE hbE habE
  have hge : 32 ≤ Nat.card Ŝ := by
    rw [← card_barOf hŜM hŜ.isPGroup, hŜbar.card_eq]
    exact h32.trans (card_le_twoPart hU2 hU)
  have hβc : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ centralizer ({g * t * g⁻¹} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hτM).symm
  exact EndB.false_of_conj_t_twoPart hKF hs (hL.orderOf_w hZ) (hL.card_T hZ) (hL.card_S_le hZ)
    hβc hŜ.le hŜ.isPGroup hŜ.card_eq (by omega) (by omega)

end EndB.LLayer

end CFSG.ComponentClassification.HarrisLit
