module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415J
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Q

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup

namespace L415

theorem comm_of_inf_eq {G : Type*} [Group G] [Finite G] {D B : Subgroup G}
    (hD : IsPGroup 2 D) {z₁ : G} (hcen : ∀ c ∈ D, (∀ d ∈ D, c * d = d * c) → c = 1 ∨ c = z₁)
    (hz₁B : z₁ ∉ B) (hBn : ∀ d ∈ D, ∀ b ∈ B, d * b * d⁻¹ ∈ B) {b : G} (hb : b ∈ B)
    (hbD : ∀ d ∈ D, b * d * b⁻¹ ∈ D) : ∀ d ∈ D, d * b = b * d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥D := hD.isNilpotent
  set N := (B ⊓ D).subgroupOf D with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    have hn' : (n : G) ∈ B ⊓ D := hn
    show ((g * n * g⁻¹ : ↥D) : G) ∈ B ⊓ D
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact mem_inf.mpr ⟨hBn g g.2 n (mem_inf.mp hn').1,
      mul_mem (mul_mem g.2 (mem_inf.mp hn').2) (inv_mem g.2)⟩⟩
  have hNbot : N = ⊥ := by
    by_contra hne
    have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
    obtain ⟨⟨c, hcN, hcZ⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
    have hcN' : (c : G) ∈ B ⊓ D := hcN
    rcases hcen c c.2 (fun d hd => congrArg Subtype.val ((mem_center_iff.mp hcZ) ⟨d, hd⟩).symm)
      with h2 | h2
    · exact hc1 (Subtype.ext (Subtype.ext h2))
    · exact hz₁B (h2 ▸ (mem_inf.mp hcN').1)
  intro d hd
  have h1 : d * b * d⁻¹ * b⁻¹ ∈ B ⊓ D := by
    refine mem_inf.mpr ⟨mul_mem (hBn d hd b hb) (inv_mem hb), ?_⟩
    rw [show d * b * d⁻¹ * b⁻¹ = d * (b * d⁻¹ * b⁻¹) by group]
    exact mul_mem hd (hbD _ (inv_mem hd))
  have h2 : (⟨d * b * d⁻¹ * b⁻¹, (mem_inf.mp h1).2⟩ : ↥D) ∈ N := h1
  rw [hNbot, mem_bot] at h2
  have h3 : d * b * d⁻¹ * b⁻¹ = 1 := congrArg Subtype.val h2
  calc d * b = d * b * d⁻¹ * b⁻¹ * (b * d) := by group
    _ = b * d := by rw [h3, one_mul]

namespace IsProd

variable {G : Type} [Group G] [Finite G] {E K₁ K₂ : Subgroup G} {s : G}

omit [Finite G] in
theorem symm (h : IsProd E K₁ K₂ s) : IsProd E K₂ K₁ s⁻¹ where
  sup_eq := by rw [sup_comm]; exact h.sup_eq
  inf_eq := by rw [inf_comm]; exact h.inf_eq
  le_centralizer := fun b hb => Subgroup.mem_centralizer_iff.mpr fun a ha => h.comm ha hb
  map_conj := by
    rw [inv_inv, ← h.map_conj, Subgroup.map_map]
    have : (MulAut.conj s).toMonoidHom.comp (MulAut.conj s⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [this, Subgroup.map_id]
  simple := h.simple₂
  nonabelian := h.nonabelian₂

theorem map_K₁_of_abelian (h : IsProd E K₁ K₂ s) (hE : E.Normal) {P B : Subgroup G}
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBn : ∀ d ∈ P ⊓ K₁, ∀ b ∈ B, d * b * d⁻¹ ∈ B)
    (hnab : ∃ a ∈ P ⊓ K₁, ∃ b ∈ P ⊓ K₁, a * b ≠ b * a) {b : G} (hb : b ∈ B) :
    K₁.map (MulAut.conj b).toMonoidHom = K₁ := by
  rcases h.conj_cases hE b with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨d, hd, d', hd', hdd⟩ := hnab
    apply hdd
    have hbK : ∀ k ∈ K₁, b * k * b⁻¹ ∈ K₂ := fun k hk => by rw [← h1]; exact ⟨k, hk, rfl⟩
    have hc : ∀ e ∈ P ⊓ K₁, e * (b * e⁻¹ * b⁻¹) ∈ B := fun e he => by
      rw [show e * (b * e⁻¹ * b⁻¹) = (e * b * e⁻¹) * b⁻¹ by group]
      exact mul_mem (hBn e he b hb) (inv_mem hb)
    have hk₂ : ∀ e ∈ P ⊓ K₁, b * e⁻¹ * b⁻¹ ∈ K₂ := fun e he => hbK _ (inv_mem (mem_inf.mp he).2)
    have h2 := hBc _ (hc d hd) _ (hc d' hd')
    have hx : d' * (b * d⁻¹ * b⁻¹) = (b * d⁻¹ * b⁻¹) * d' := h.comm (mem_inf.mp hd').2 (hk₂ d hd)
    have hx' : d * (b * d'⁻¹ * b⁻¹) = (b * d'⁻¹ * b⁻¹) * d :=
      h.comm (mem_inf.mp hd).2 (hk₂ d' hd')
    have h3 : d * d' * ((b * d⁻¹ * b⁻¹) * (b * d'⁻¹ * b⁻¹)) =
        d' * d * ((b * d'⁻¹ * b⁻¹) * (b * d⁻¹ * b⁻¹)) := by
      calc d * d' * ((b * d⁻¹ * b⁻¹) * (b * d'⁻¹ * b⁻¹)) =
          d * (d' * (b * d⁻¹ * b⁻¹)) * (b * d'⁻¹ * b⁻¹) := by group
        _ = d * ((b * d⁻¹ * b⁻¹) * d') * (b * d'⁻¹ * b⁻¹) := by rw [hx]
        _ = d * (b * d⁻¹ * b⁻¹) * (d' * (b * d'⁻¹ * b⁻¹)) := by group
        _ = d' * (b * d'⁻¹ * b⁻¹) * (d * (b * d⁻¹ * b⁻¹)) := h2
        _ = d' * (d * (b * d'⁻¹ * b⁻¹)) * (b * d⁻¹ * b⁻¹) := by
            rw [show d' * (b * d'⁻¹ * b⁻¹) * (d * (b * d⁻¹ * b⁻¹)) =
              d' * ((b * d'⁻¹ * b⁻¹) * d) * (b * d⁻¹ * b⁻¹) by group, ← hx']
        _ = d' * d * ((b * d'⁻¹ * b⁻¹) * (b * d⁻¹ * b⁻¹)) := by group
    exact (h.eq_of_mul_eq (mul_mem (mem_inf.mp hd).2 (mem_inf.mp hd').2)
      (mul_mem (mem_inf.mp hd').2 (mem_inf.mp hd).2) (mul_mem (hk₂ d hd) (hk₂ d' hd'))
      (mul_mem (hk₂ d' hd') (hk₂ d hd)) h3).1

omit [Finite G] in
theorem sq_comm_of_fix' [Finite G] (hA : AutPSL2RCentralizerInput) {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Subgroup G} (hlie : Blueprint.LieModel ↥K .PSL 2 p n) {P : Subgroup G}
    (hPK : IsSylowOf 2 (P ⊓ K) K) (h8 : 8 ≤ Nat.card ↥(P ⊓ K)) {y : G}
    (hy2 : ∃ k : ℕ, orderOf y = 2 ^ k) (hyN : y ∈ normalizer (K : Set G))
    (hfix : ∀ d ∈ P ⊓ K, d * y = y * d) : ∀ k ∈ K, y ^ 2 * k = k * y ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a := normalizerConj K ⟨y, hyN⟩ with ha
  have hao : ∃ k : ℕ, orderOf a = 2 ^ k := by
    have h1 : orderOf a ∣ orderOf (⟨y, hyN⟩ : ↥(normalizer (K : Set G))) := orderOf_map_dvd _ _
    obtain ⟨j, hj⟩ := hy2
    rw [Subgroup.orderOf_mk, hj] at h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact ⟨k, hk⟩
  obtain ⟨Q, hQ⟩ := hPK
  have hQR : (Q : Subgroup ↥K) = (P ⊓ K).subgroupOf K := by
    rw [← hQ]
    exact (comap_map_eq_self_of_injective K.subtype_injective _).symm
  have hcardR : 8 ≤ Nat.card ↥((P ⊓ K).subgroupOf K) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : P ⊓ K ≤ K)).toEquiv]
    exact h8
  have hfixa : ∀ x ∈ (P ⊓ K).subgroupOf K, a x = x := by
    intro x hx
    apply Subtype.ext
    rw [ha, normalizerConj_apply]
    have h1 := hfix x hx
    calc y * (x : G) * y⁻¹ = (y * x) * y⁻¹ := by group
      _ = (x * y) * y⁻¹ := by rw [h1]
      _ = x := by group
  have h1 := hA ↥K p n hp hp2 hlie _ ⟨Q, hQR⟩ hcardR a hao hfixa
  intro k hk
  have h2 := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : G)) h1
  simp only [MulAut.mul_apply, MulAut.one_apply] at h2
  rw [ha, normalizerConj_apply, normalizerConj_apply] at h2
  calc y ^ 2 * k = (y * (y * k * y⁻¹) * y⁻¹) * y ^ 2 := by rw [sq]; group
    _ = k * y ^ 2 := by rw [h2]

theorem dihedral_facts (h : IsProd E K₁ K₂ s) (hE : E.Normal) {P : Subgroup G}
    (hP : IsSylowOf 2 P ⊤) (hs : s * s = 1) (hsP : s ∈ P) {D : Subgroup G}
    (hD : IsSylowOf 2 D (E ⊓ centralizer {s})) (hDP : D ≤ P) {m : ℕ} (hm : 2 ≤ m)
    (eD : ↥D ≃* DihedralGroup (2 ^ m)) {z₁ : G} (hz₁ : z₁ ∈ P ⊓ K₁)
    (hzc : ∀ d ∈ D, z₁ * (s⁻¹ * z₁ * s) * d = d * (z₁ * (s⁻¹ * z₁ * s)))
    (hz1 : z₁ * (s⁻¹ * z₁ * s) ≠ 1) :
    (∃ a ∈ P ⊓ K₁, ∃ b ∈ P ⊓ K₁, a * b ≠ b * a) ∧
      (∀ c ∈ P ⊓ K₁, (∀ d ∈ P ⊓ K₁, c * d = d * c) → c = 1 ∨ c = z₁) ∧
      ∃ v ∈ P ⊓ K₁, orderOf v = 4 ∧ v ^ 2 = z₁ ∧
        ∀ x ∈ P ⊓ K₁, orderOf x = 4 → x ∈ zpowers v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPD : P ⊓ (E ⊓ centralizer {s}) = D :=
    hD.eq_of_le (le_inf hDP hD.le) inf_le_right (hP.isPGroup.to_le inf_le_left)
  set z := z₁ * (s⁻¹ * z₁ * s) with hz
  have hzD : z ∈ D := h.diag_mem hs hsP hPD hz₁
  have hsurj : ∀ y ∈ D, ∃ c ∈ P ⊓ K₁, y = c * (s⁻¹ * c * s) := by
    intro y hy
    have hy' : y ∈ P ⊓ (E ⊓ centralizer {s}) := by rw [hPD]; exact hy
    exact h.exists_diag hE hP hs ⟨hy'.1, hy'.2.1⟩ (mem_centralizer_singleton_iff.mp hy'.2.2).symm
  have hδ : ∀ c (hc : c ∈ P ⊓ K₁), h.diag ⟨c, (mem_inf.mp hc).2⟩ ∈ D := fun c hc =>
    h.diag_mem hs hsP hPD hc
  have hmul : ∀ (a b : G) (ha : a ∈ K₁) (hb : b ∈ K₁),
      h.diag ⟨a * b, mul_mem ha hb⟩ = h.diag ⟨a, ha⟩ * h.diag ⟨b, hb⟩ := fun a b ha hb => by
    rw [← map_mul]
    rfl
  have hinj : ∀ (a b : G) (ha : a ∈ K₁) (hb : b ∈ K₁), h.diag ⟨a, ha⟩ = h.diag ⟨b, hb⟩ →
      a = b := fun a b ha hb hab => congrArg Subtype.val (h.diag_injective hab)
  refine ⟨?_, ?_, ?_⟩
  ·
    by_contra hab
    push Not at hab
    have h1 : ∀ y ∈ D, ∀ y' ∈ D, y * y' = y' * y := by
      intro y hy y' hy'
      obtain ⟨c, hc, rfl⟩ := hsurj y hy
      obtain ⟨c', hc', rfl⟩ := hsurj y' hy'
      have h2 := hmul c c' (mem_inf.mp hc).2 (mem_inf.mp hc').2
      have h3 := hmul c' c (mem_inf.mp hc').2 (mem_inf.mp hc).2
      rw [IsProd.diag_apply, IsProd.diag_apply, IsProd.diag_apply] at h2 h3
      rw [← h2, ← h3]
      simp only [hab c hc c' hc']
    have h2 := h1 _ (eD.symm (r 1)).2 _ (eD.symm (sr 0)).2
    have h3 : eD.symm (r 1) * eD.symm (sr 0) = eD.symm (sr 0) * eD.symm (r 1) := Subtype.ext h2
    have h4 := congrArg eD h3
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, r_mul_sr,
      sr_mul_r, sr.injEq, zero_sub, zero_add] at h4
    have h5 : ((2 : ℕ) : ZMod (2 ^ m)) = 0 := by
      rw [Nat.cast_ofNat]
      linear_combination -h4
    rw [ZMod.natCast_eq_zero_iff] at h5
    have h6 := Nat.le_of_dvd (by norm_num) h5
    have h7 : 4 ≤ 2 ^ m :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  ·
    intro c hc hcc
    have hzc' : (⟨z, hzD⟩ : ↥D) ∈ center ↥D :=
      mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2).symm
    have hδc : (⟨_, hδ c hc⟩ : ↥D) ∈ center ↥D := by
      refine mem_center_iff.mpr fun g => Subtype.ext ?_
      obtain ⟨c', hc', hg⟩ := hsurj g g.2
      show (g : G) * h.diag ⟨c, (mem_inf.mp hc).2⟩ = h.diag ⟨c, (mem_inf.mp hc).2⟩ * g
      rw [hg, show c' * (s⁻¹ * c' * s) = h.diag ⟨c', (mem_inf.mp hc').2⟩ from rfl,
        ← hmul _ _ (mem_inf.mp hc').2 (mem_inf.mp hc).2,
        ← hmul _ _ (mem_inf.mp hc).2 (mem_inf.mp hc').2]
      congr 2
      exact (hcc c' hc').symm
    rcases eq_of_mem_center_dihedral eD hm hzc' (fun h1 => hz1 (congrArg Subtype.val h1))
      hδc with h1 | h1
    · left
      have h2 : h.diag ⟨c, (mem_inf.mp hc).2⟩ = h.diag 1 := by
        rw [map_one]
        exact congrArg Subtype.val h1
      exact congrArg Subtype.val (h.diag_injective h2)
    · right
      have h2 : h.diag ⟨c, (mem_inf.mp hc).2⟩ = h.diag ⟨z₁, (mem_inf.mp hz₁).2⟩ := by
        rw [IsProd.diag_apply h ⟨z₁, (mem_inf.mp hz₁).2⟩]
        exact congrArg Subtype.val h1
      exact congrArg Subtype.val (h.diag_injective h2)
  ·
    have hDp : IsPGroup 2 D := hP.isPGroup.to_le hDP
    have hshape : IsCyclic ↥D ∨ ∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥D ≃* DihedralGroup (2 ^ k)) :=
      Or.inr ⟨m, by omega, ⟨eD⟩⟩
    have hzc' : (⟨z, hzD⟩ : ↥D) ∈ center ↥D :=
      mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2).symm
    have hz2 : z * z = 1 := by
      have hz2c : (⟨z, hzD⟩ : ↥D) * ⟨z, hzD⟩ ∈ center ↥D := mul_mem hzc' hzc'
      rcases eq_of_mem_center_dihedral eD hm hzc' (fun h1 => hz1 (congrArg Subtype.val h1))
        hz2c with h1 | h1
      · exact congrArg Subtype.val h1
      · exfalso
        apply hz1
        have h2 : z * z = z := congrArg Subtype.val h1
        calc z = z * z * z⁻¹ := by group
          _ = z * z⁻¹ := by rw [h2]
          _ = 1 := mul_inv_cancel z
    have hq : ((eD.symm (r 1) : ↥D) : G) * (eD.symm (r 1) : ↥D) ≠ 1 := by
      intro h1
      have h2 : orderOf ((eD.symm (r 1) : ↥D) : G) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h1)
      rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq eD, MulEquiv.apply_symm_apply,
        orderOf_r_one] at h2
      have h3 := Nat.le_of_dvd (by norm_num) h2
      have h4 : 4 ≤ 2 ^ m :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
    obtain ⟨v', hv'D, hv'o, hv'2, hv'4⟩ := exists_four hDp hshape hzD hz2 hz1
      (fun x hx => (hzc x hx).symm) (eD.symm (r 1)).2 hq
    obtain ⟨v, hv, hvv⟩ := hsurj v' hv'D
    have hvd : h.diag ⟨v, (mem_inf.mp hv).2⟩ = v' := by rw [IsProd.diag_apply, ← hvv]
    have hord : ∀ (c : G) (hc : c ∈ K₁), orderOf (h.diag ⟨c, hc⟩) = orderOf c := by
      intro c hc
      have h1 := orderOf_injective h.diag h.diag_injective ⟨c, hc⟩
      rw [Subgroup.orderOf_mk] at h1
      exact h1
    refine ⟨v, hv, ?_, ?_, fun x hx hx4 => ?_⟩
    · rw [← hord v (mem_inf.mp hv).2, hvd, hv'o]
    · apply hinj _ _ (pow_mem (mem_inf.mp hv).2 2) (mem_inf.mp hz₁).2
      rw [show (⟨v ^ 2, pow_mem (mem_inf.mp hv).2 2⟩ : ↥K₁) = ⟨v, (mem_inf.mp hv).2⟩ ^ 2 from rfl,
        map_pow, hvd, hv'2, IsProd.diag_apply]
    · have hxd : h.diag ⟨x, (mem_inf.mp hx).2⟩ ∈ zpowers v' :=
        hv'4 _ (hδ x hx) (by rw [hord, hx4])
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hxd
      rw [mem_zpowers_iff]
      refine ⟨k, hinj _ _ (zpow_mem (mem_inf.mp hv).2 k) (mem_inf.mp hx).2 ?_⟩
      rw [show (⟨v ^ k, zpow_mem (mem_inf.mp hv).2 k⟩ : ↥K₁) = ⟨v, (mem_inf.mp hv).2⟩ ^ k from
        Subtype.ext (by simp), map_zpow, hvd, hk]

end IsProd

end L415

end CFSG.ComponentClassification.HarrisLit
