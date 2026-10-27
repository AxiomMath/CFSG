module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2324
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi23FiveRow
import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi23FiveGen

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSpor5

section General

variable {G : Type*} [Group G]

theorem card_sup_of_commute {H K : Subgroup G} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
    (hHK : H ⊓ K = ⊥) : Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have comm : ∀ (m : H) (n : K), Commute (H.subtype m) (K.subtype n) :=
    fun m n => hc m m.2 n n.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod H.subtype K.subtype comm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨H.subtype_injective, K.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hHK
  have hrange : (MonoidHom.noncommCoprod H.subtype K.subtype comm).range = H ⊔ K := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem conj_inv_mul_comm {h w d : G} (hwe : w * (h * d * h⁻¹) = (h * d * h⁻¹) * w) :
    h⁻¹ * w * h * d = d * (h⁻¹ * w * h) := by
  calc h⁻¹ * w * h * d = h⁻¹ * (w * (h * d * h⁻¹)) * h := by group
    _ = h⁻¹ * ((h * d * h⁻¹) * w) * h := by rw [hwe]
    _ = d * (h⁻¹ * w * h) := by group

theorem orderOf_inv_mul_mul (h w : G) : orderOf (h⁻¹ * w * h) = orderOf w := by
  have := (MulAut.conj h⁻¹).orderOf_eq w
  simpa [MulAut.conj_apply] using this

theorem zpowers_conj_eq {a b : G} (h : G)
    (hab : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.zpowers (h * a * h⁻¹) = Subgroup.zpowers (h * b * h⁻¹) := by
  have e : ∀ c : G, Subgroup.zpowers (h * c * h⁻¹) =
      (Subgroup.zpowers c).map (MulAut.conj h).toMonoidHom := fun c => by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [e a, e b, hab]

end General

section Perm

def cyc5 : Equiv.Perm (Fin 12) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4

def cyc5' : Equiv.Perm (Fin 12) :=
  Equiv.swap 5 6 * Equiv.swap 6 7 * Equiv.swap 7 8 * Equiv.swap 8 9

noncomputable def iota7 : Equiv.Perm (Fin 7) →* Equiv.Perm (Fin 12) :=
  Equiv.Perm.viaEmbeddingHom (Fin.natAddEmb 5 : Fin 7 ↪ Fin 12)

theorem cyc5_pow_five : cyc5 ^ 5 = 1 := by decide

theorem cyc5_ne_one : cyc5 ≠ 1 := by decide

theorem cyc5_zero : cyc5 0 = 1 := by decide

theorem cyc5_fix : ∀ i : Fin 12, 5 ≤ i.val → cyc5 i = i := by decide

theorem cyc5'_pow_five : cyc5' ^ 5 = 1 := by decide

theorem cyc5_comm_cyc5' : cyc5 * cyc5' = cyc5' * cyc5 := by decide

theorem cyc5'_ne_pow : ∀ k < 5, cyc5' ≠ cyc5 ^ k := by decide

theorem adjSwap_ten_comm_cyc5 :
    CFSG.Permutation.SymmetricCoxeter.adjSwap 11 10 * cyc5 =
      cyc5 * CFSG.Permutation.SymmetricCoxeter.adjSwap 11 10 := by
  rw [CFSG.Permutation.SymmetricCoxeter.adjSwap_of_lt (by norm_num)]
  decide

theorem adjSwap_ten_comm_cyc5' :
    CFSG.Permutation.SymmetricCoxeter.adjSwap 11 10 * cyc5' =
      cyc5' * CFSG.Permutation.SymmetricCoxeter.adjSwap 11 10 := by
  rw [CFSG.Permutation.SymmetricCoxeter.adjSwap_of_lt (by norm_num)]
  decide

theorem iota7_apply_of_lt (σ : Equiv.Perm (Fin 7)) {i : Fin 12} (hi : i.val < 5) :
    iota7 σ i = i := by
  unfold iota7
  rw [Equiv.Perm.viaEmbeddingHom_apply]
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨j, hj⟩
  have h : 5 + j.val = i.val := congrArg Fin.val hj
  omega

theorem iota7_injective : Function.Injective iota7 := Equiv.Perm.viaEmbeddingHom_injective _

theorem iota7_commute_cyc5 (σ : Equiv.Perm (Fin 7)) : iota7 σ * cyc5 = cyc5 * iota7 σ := by
  have hd : (iota7 σ).Disjoint cyc5 := by
    intro i
    by_cases hi : i.val < 5
    · exact Or.inl (iota7_apply_of_lt σ hi)
    · exact Or.inr (cyc5_fix i (by omega))
  exact hd.commute

theorem iota7_ne_cyc5 (σ : Equiv.Perm (Fin 7)) : iota7 σ ≠ cyc5 := by
  intro h
  have h1 := iota7_apply_of_lt σ (i := 0) (by decide)
  rw [h, cyc5_zero] at h1
  exact absurd h1 (by decide)

theorem sign_comm_eq_one (g s : Equiv.Perm (Fin 12)) :
    g * s * g⁻¹ * s⁻¹ ∈ alternatingGroup (Fin 12) := by
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul, map_mul, map_inv, map_inv,
    mul_right_comm (Equiv.Perm.sign g), mul_inv_cancel, one_mul, mul_inv_cancel]

theorem injective_of_alt_ne_one {H : Type*} [Group H] (ψ : Equiv.Perm (Fin 12) →* H)
    {τ : Equiv.Perm (Fin 12)} (hτ : τ ∈ alternatingGroup (Fin 12)) (hψτ : ψ τ ≠ 1) :
    Function.Injective ψ := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 12)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : (ψ.ker.subgroupOf (alternatingGroup (Fin 12))).Normal :=
    (ψ.normal_ker).subgroupOf (alternatingGroup (Fin 12))
  have hKA : (ψ.ker.subgroupOf (alternatingGroup (Fin 12))) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ψ.ker.subgroupOf (alternatingGroup (Fin 12)))
        with h | h
    · exact h
    · exfalso
      have hmem : (⟨τ, hτ⟩ : alternatingGroup (Fin 12)) ∈ ψ.ker.subgroupOf (alternatingGroup (Fin 12)) := by
        rw [h]; exact Subgroup.mem_top _
      exact hψτ (Subgroup.mem_subgroupOf.1 hmem)
  rw [injective_iff_map_eq_one]
  intro s hs
  have hcomm : ∀ g : Equiv.Perm (Fin 12), g * s = s * g := by
    intro g
    have hk : g * s * g⁻¹ * s⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hs]
      group
    have hmem : (⟨_, sign_comm_eq_one g s⟩ : alternatingGroup (Fin 12)) ∈
        ψ.ker.subgroupOf (alternatingGroup (Fin 12)) := Subgroup.mem_subgroupOf.2 hk
    rw [hKA, Subgroup.mem_bot] at hmem
    have h1 : g * s * g⁻¹ * s⁻¹ = 1 := congrArg Subtype.val hmem
    calc g * s = g * s * g⁻¹ * s⁻¹ * (s * g) := by group
      _ = s * g := by rw [h1, one_mul]
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.one_apply]
  by_contra hi
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 12, k ≠ i ∧ k ≠ s i := by
    have key : ∀ a b : Fin 12, ∃ k : Fin 12, k ≠ a ∧ k ≠ b := by decide
    exact key i (s i)
  have h1 := congrArg (fun f : Equiv.Perm (Fin 12) => f i) (hcomm (Equiv.swap (s i) k))
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left] at h1
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) hki.symm] at h1
  exact hkj h1

end Perm

section Structure

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_perm7 : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem alt7_simple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem alt7_nonab : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a := by
  by_contra h
  push Not at h
  have htop : Subgroup.center (alternatingGroup (Fin 7)) = ⊤ :=
    eq_top_iff.2 fun z _ => Subgroup.mem_center_iff.2 fun g => h g z
  rw [alternatingGroup.center_eq_bot (by simp)] at htop
  have h1 : Nat.card (⊥ : Subgroup (alternatingGroup (Fin 7))) =
      Nat.card (⊤ : Subgroup (alternatingGroup (Fin 7))) := by rw [htop]
  rw [Subgroup.card_bot, Subgroup.card_top, card_alt7] at h1
  norm_num at h1

theorem le_normalizer_of_conj_mem {S : Type*} [Group S] {H L : Subgroup S}
    (h : ∀ g ∈ H, ∀ l ∈ L, g * l * g⁻¹ ∈ L) : H ≤ Subgroup.normalizer (L : Set S) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨h g hg l, fun hl => ?_⟩
  have := h g⁻¹ (H.inv_mem hg) _ hl
  simpa [mul_assoc] using this

variable {S : Type} [Group S] [Finite S]

theorem layer_of_model (ψ : Equiv.Perm (Fin 12) →* S) (hψ : Function.Injective ψ) {x : S}
    (hx : Subgroup.zpowers x = Subgroup.zpowers (ψ cyc5))
    (hcard : Nat.card (Subgroup.centralizer ({x} : Set S)) ≤ 25200)
    (hcore : GLAPPrimeCore 5 ↥(Subgroup.centralizer ({x} : Set S)) = ⊥) :
    ∃ Λ : Subgroup S, GLAPComponent 5 (Subgroup.centralizer ({x} : Set S)) Λ ∧
      (∀ H : Subgroup S, GLAPComponent 5 (Subgroup.centralizer ({x} : Set S)) H → H = Λ) ∧
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.IsAltType 7 ↥Λ ∧ x ∉ Λ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alt7_simple
  set φ : Equiv.Perm (Fin 7) →* S := ψ.comp iota7 with hφ
  have hφinj : Function.Injective φ := hψ.comp iota7_injective
  set C : Subgroup S := Subgroup.centralizer ({x} : Set S) with hC
  set Sg : Subgroup S := φ.range with hSg
  set Λ : Subgroup S := (alternatingGroup (Fin 7)).map φ with hΛ
  have hx0o : orderOf (ψ cyc5) = 5 := by
    rw [orderOf_injective ψ hψ cyc5]
    exact orderOf_eq_prime cyc5_pow_five cyc5_ne_one
  have hxo : orderOf x = 5 := by
    rw [← Nat.card_zpowers, hx, Nat.card_zpowers, hx0o]
  have hcomm0 : ∀ a ∈ Sg, a * ψ cyc5 = ψ cyc5 * a := by
    rintro _ ⟨σ, rfl⟩
    simp only [hφ, MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, iota7_commute_cyc5]
  have hcommx : ∀ a ∈ Sg, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    rw [hx]
    exact GL83.CompFam.zpowers_commute hcomm0
  have hx0Sg : ψ cyc5 ∉ Sg := by
    rintro ⟨σ, hσ⟩
    exact iota7_ne_cyc5 σ (hψ hσ)
  have hxSg : x ∉ Sg := by
    intro hxS
    apply hx0Sg
    have hle : Subgroup.zpowers x ≤ Sg := (Subgroup.zpowers_le).2 hxS
    rw [hx] at hle
    exact hle (Subgroup.mem_zpowers _)
  have hinf : Sg ⊓ Subgroup.zpowers x = ⊥ := GL83.CompFam.inf_zpowers_eq_bot hxo hxSg
  have hSgcard : Nat.card Sg = 5040 := by
    rw [← card_perm7]
    exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  have hsup : Nat.card ↥(Sg ⊔ Subgroup.zpowers x) = 25200 := by
    rw [card_sup_of_commute hcommx hinf, hSgcard, Nat.card_zpowers, hxo]
  have hSgC : Sg ≤ C := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcommx a ha x (Subgroup.mem_zpowers x))
  have hxC : Subgroup.zpowers x ≤ C :=
    (Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hCeq : Sg ⊔ Subgroup.zpowers x = C :=
    Subgroup.eq_of_le_of_card_ge (sup_le hSgC hxC) (by rw [hsup]; exact hcard)
  have hΛSg : Λ ≤ Sg := Subgroup.map_le_range _ _
  have hΛC : Λ ≤ C := hΛSg.trans hSgC
  have hSgN : Sg ≤ Subgroup.normalizer (Λ : Set S) := by
    refine le_normalizer_of_conj_mem ?_
    rintro _ ⟨σ, rfl⟩ _ ⟨a, ha, rfl⟩
    refine ⟨σ * a * σ⁻¹, (alternatingGroup.normal (α := Fin 7)).conj_mem a ha σ, ?_⟩
    simp only [map_mul, map_inv]
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (Λ : Set S) := by
    refine le_normalizer_of_conj_mem ?_
    intro g hg l hl
    rw [← hcommx l (hΛSg hl) g hg, mul_inv_cancel_right]
    exact hl
  have hCN : C ≤ Subgroup.normalizer (Λ : Set S) := hCeq ▸ sup_le hSgN hxN
  have hΛn : ∀ g ∈ C, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ := fun g hg l hl =>
    (Subgroup.mem_normalizer_iff.1 (hCN hg) l).1 hl
  set eΛ : ↥Λ ≃* ↥(alternatingGroup (Fin 7)) :=
    (Subgroup.equivMapOfInjective (alternatingGroup (Fin 7)) φ hφinj).symm with heΛ
  haveI hΛs : IsSimpleGroup ↥Λ := eΛ.isSimpleGroup
  have hΛnab : ∃ a b : ↥Λ, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := alt7_nonab
    refine ⟨eΛ.symm a, eΛ.symm b, fun h => hab ?_⟩
    have := congrArg eΛ h
    simpa using this
  have hΛq : CFSG.Open.IsQuasisimple ↥Λ :=
    CFSG.HardMathSupport.Dickson.I271.isOpenQuasisimple_of_simple_nonab hΛnab
  have hΛZ : Subgroup.center ↥Λ = ⊥ :=
    CFSG.HardMathSupport.Dickson.I271.center_eq_bot_of_simple_nonab hΛnab
  have hΛcard : Nat.card Λ = 2520 := by
    rw [Nat.card_congr eΛ.toEquiv, card_alt7]
  set Zc : Subgroup S := C ⊓ Subgroup.centralizer (Λ : Set S) with hZc
  have hZcomm : ∀ z ∈ Zc, ∀ l ∈ Λ, z * l = l * z := fun z hz l hl =>
    (Subgroup.mem_centralizer_iff.1 hz.2 l hl).symm
  have hZinf : Zc ⊓ Λ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzc : (⟨z, hz.2⟩ : ↥Λ) ∈ Subgroup.center ↥Λ := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hZcomm z hz.1 l l.2).symm
    rw [hΛZ, Subgroup.mem_bot] at hzc
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hzc)
  have hZcard : Nat.card Zc ≤ 10 := by
    have h1 : Nat.card ↥(Zc ⊔ Λ) ≤ Nat.card C :=
      Subgroup.card_le_of_le (sup_le inf_le_left hΛC)
    rw [card_sup_of_commute hZcomm hZinf, hΛcard] at h1
    omega
  have hZsolv : Group.IsSolvable ↥Zc :=
    CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega)
  refine ⟨Λ, CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal_quasisimple hΛC hΛn hΛq hcore,
    fun H hH => CFSG.HardMathSupport.Dickson.I271.eq_of_glaPComponent_of_normal_quasisimple_solvable
      Nat.prime_five hΛC hΛn hΛq hcore hZsolv hH, ⟨eΛ⟩, fun hxΛ => hxSg (hΛSg hxΛ)⟩

end Structure

section Fi22

open CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Monster.B.Co2

theorem fi22_line_conj (t : Equiv.Perm (Fin 3510)) (ht : t ∈ fi22P) (hto : orderOf t = 5) :
    ∃ y ∈ fi22P, Subgroup.zpowers (y * t * y⁻¹) = Subgroup.zpowers (fi22FiveLine 0) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, -, -, hQsyl⟩, ⟨hlinesSet, -⟩, -, -⟩ :=
    R3E_Fi22_full_five_centralizers_common_outer_involution
  have hQ := card_eq_of_sylow_subgroupOf hQP hQsyl
  have hlines := lines_of_eq hlinesSet
  obtain ⟨g, hgP, hgQ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.exists_conj_mem_of_full hQP hQ ht hto
  have huo : orderOf (g⁻¹ * t * g) = 5 := by
    have := (MulAut.conj g⁻¹ : Equiv.Perm (Fin 3510) ≃* Equiv.Perm (Fin 3510)).orderOf_eq t
    simpa [MulAut.conj_apply, hto] using this
  obtain ⟨j, hj⟩ := hlines (Subgroup.zpowers (g⁻¹ * t * g)) ((Subgroup.zpowers_le).2 hgQ)
    (by rw [Nat.card_zpowers, huo])
  refine ⟨permOfArr 3510 (fi22FiveHArr j) * g⁻¹,
    fi22P.mul_mem (fi22FiveH_mem_P j) (fi22P.inv_mem hgP), ?_⟩
  have e1 : permOfArr 3510 (fi22FiveHArr j) * g⁻¹ * t * (permOfArr 3510 (fi22FiveHArr j) * g⁻¹)⁻¹ =
      permOfArr 3510 (fi22FiveHArr j) * (g⁻¹ * t * g) * (permOfArr 3510 (fi22FiveHArr j))⁻¹ := by
    group
  rw [e1, zpowers_conj_eq _ hj, fi22FiveH_conj j]

theorem fi22_fusion {t₁ t₂ : Equiv.Perm (Fin 3510)} (h₁ : t₁ ∈ fi22P) (h₂ : t₂ ∈ fi22P)
    (o₁ : orderOf t₁ = 5) (o₂ : orderOf t₂ = 5) :
    ∃ y ∈ fi22P, y * t₁ * y⁻¹ ∈ Subgroup.zpowers t₂ := by
  obtain ⟨y₁, hy₁, e₁⟩ := fi22_line_conj t₁ h₁ o₁
  obtain ⟨y₂, hy₂, e₂⟩ := fi22_line_conj t₂ h₂ o₂
  refine ⟨y₂⁻¹ * y₁, fi22P.mul_mem (fi22P.inv_mem hy₂) hy₁, ?_⟩
  have hmem : y₁ * t₁ * y₁⁻¹ ∈ Subgroup.zpowers (y₂ * t₂ * y₂⁻¹) := by
    rw [e₂, ← e₁]
    exact Subgroup.mem_zpowers _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
  refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
  rw [conj_zpow] at hn
  calc t₂ ^ n = y₂⁻¹ * (y₂ * t₂ ^ n * y₂⁻¹) * y₂ := by group
    _ = y₂⁻¹ * y₁ * t₁ * (y₂⁻¹ * y₁)⁻¹ := by rw [hn]; group

end Fi22

section Cd

open CFSG.Sporadic.Fi23 CFSG.Monster.B.Fischer

theorem pow_five_of_comm {G : Type*} [Group G] {u c : G} (huc : u * c = c * u) (hu : u ^ 2 = 1)
    (hc : c ^ 5 = 1) : (u * c) ^ 5 = u := by
  have h : Commute u c := huc
  rw [h.mul_pow, hc, mul_one, show (5 : ℕ) = 2 * 2 + 1 from rfl, pow_succ, pow_mul, hu, one_pow,
    one_mul]

theorem cd_fusion {a b : CFSG.Sporadic.Fi23.J} (ha : a * d = d * a) (hb : b * d = d * b) (hao : orderOf a = 5)
    (hbo : orderOf b = 5) : ∃ k : CFSG.Sporadic.Fi23.J, k * d = d * k ∧ k * a * k⁻¹ ∈ Subgroup.zpowers b := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set a' : Cd := ⟨a, mem_Cd.2 ha⟩ with ha'
  set b' : Cd := ⟨b, mem_Cd.2 hb⟩ with hb'
  have hρo : ∀ c : Cd, orderOf c = 5 → orderOf (rho c) = 5 := by
    intro c hc
    apply orderOf_eq_prime
    · rw [← map_pow, ← hc, pow_orderOf_eq_one, map_one]
    · intro h1
      have hk : c ∈ rho.ker := h1
      rw [ker_rho] at hk
      have := orderOf_dvd_of_mem_zpowers hk
      rw [hc, orderOf_dCd] at this
      norm_num at this
  have ha'o : orderOf a' = 5 := by rw [← Subgroup.orderOf_coe]; exact hao
  have hb'o : orderOf b' = 5 := by rw [← Subgroup.orderOf_coe]; exact hbo
  set E := rhoRangeEquiv with hE
  set ra : ↥rho.range := ⟨rho a', MonoidHom.mem_range.2 ⟨a', rfl⟩⟩ with hra
  set rb : ↥rho.range := ⟨rho b', MonoidHom.mem_range.2 ⟨b', rfl⟩⟩ with hrb
  have hEa : orderOf ((E ra : ↥fi22P) : Equiv.Perm (Fin 3510)) = 5 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hra, Subgroup.orderOf_mk]
    exact hρo a' ha'o
  have hEb : orderOf ((E rb : ↥fi22P) : Equiv.Perm (Fin 3510)) = 5 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hrb, Subgroup.orderOf_mk]
    exact hρo b' hb'o
  obtain ⟨y, hy, hmem⟩ := fi22_fusion (E ra).2 (E rb).2 hEa hEb
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hn' : (E rb) ^ n = ⟨y, hy⟩ * E ra * (⟨y, hy⟩ : ↥fi22P)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hn
  have hn'' : rb ^ n = E.symm ⟨y, hy⟩ * ra * (E.symm ⟨y, hy⟩)⁻¹ := by
    have := congrArg E.symm hn'
    simpa using this
  obtain ⟨k, hk⟩ := (E.symm ⟨y, hy⟩).2
  have h3 : rho (b' ^ n) = rho (k * a' * k⁻¹) := by
    have := congrArg Subtype.val hn''
    simp only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [map_zpow, map_mul, map_mul, map_inv, hk]
    exact this
  have h4 : k * a' * k⁻¹ * (b' ^ n)⁻¹ ∈ rho.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← h3, mul_inv_cancel]
  rw [ker_rho] at h4
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 h4
  set kJ : CFSG.Sporadic.Fi23.J := (k : CFSG.Sporadic.Fi23.J) with hkJ
  have hmJ : d ^ m = kJ * a * kJ⁻¹ * (b ^ n)⁻¹ := by
    have := congrArg Subtype.val hm
    simpa [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv, dCd_val] using this
  have hd2 : d ^ 2 = 1 := by rw [← orderOf_d, pow_orderOf_eq_one]
  have hd1 : d ≠ 1 := by
    intro h
    have := orderOf_d
    rw [h, orderOf_one] at this
    norm_num at this
  have hmod : d ^ m = d ^ (m % 2) := by
    have := zpow_mod_orderOf d m
    rw [orderOf_d] at this
    exact_mod_cast this.symm
  have hka : kJ * a * kJ⁻¹ = b ^ n := by
    rcases Int.emod_two_eq_zero_or_one m with h0 | h0
    · rw [hmod, h0, zpow_zero] at hmJ
      calc kJ * a * kJ⁻¹ = kJ * a * kJ⁻¹ * (b ^ n)⁻¹ * b ^ n := by group
        _ = b ^ n := by rw [← hmJ, one_mul]
    · exfalso
      rw [hmod, h0, zpow_one] at hmJ
      have h5 : (kJ * a * kJ⁻¹) ^ 5 = 1 := by
        rw [conj_pow, ← hao, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
      have h6 : kJ * a * kJ⁻¹ = d * b ^ n := by
        calc kJ * a * kJ⁻¹ = kJ * a * kJ⁻¹ * (b ^ n)⁻¹ * b ^ n := by group
          _ = d * b ^ n := by rw [← hmJ]
      have hb5 : (b ^ n) ^ 5 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm n, zpow_mul, zpow_natCast, ← hbo,
          pow_orderOf_eq_one, one_zpow]
      have hdb : d * b ^ n = b ^ n * d := (mem_Cd.1 (Cd.zpow_mem (mem_Cd.2 hb) n)).symm
      have h7 : (d * b ^ n) ^ 5 = d :=
        @pow_five_of_comm (↥CFSG.Sporadic.Fi23.J) inferInstance d (b ^ n) hdb hd2 hb5
      rw [h6, h7] at h5
      exact hd1 h5
  exact ⟨kJ, mem_Cd.1 k.2, Subgroup.mem_zpowers_iff.2 ⟨n, hka.symm⟩⟩

end Cd

section FusionJ

open CFSG.Sporadic.Fi23 CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.Permutation.SymmetricCoxeter (adjSwap adjSwap_of_lt)

theorem exists_injective_s12 :
    ∃ ψ : Equiv.Perm (Fin 12) →* CFSG.Sporadic.Fi23.J, Function.Injective ψ ∧ ψ (adjSwap 11 10) ∈ D23 := by
  obtain ⟨ψ, hψ⟩ := exists_hom_s12
  have hτ : adjSwap 11 0 * adjSwap 11 2 ∈ alternatingGroup (Fin 12) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, adjSwap_of_lt (by norm_num),
      adjSwap_of_lt (by norm_num), Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide
  have hne : ψ (adjSwap 11 0 * adjSwap 11 2) ≠ 1 := by
    rw [map_mul, hψ 0 (by norm_num), hψ 2 (by norm_num)]
    exact sEl_zero_mul_two_ne_one
  refine ⟨ψ, injective_of_alt_ne_one ψ hτ hne, ?_⟩
  rw [hψ 10 (by norm_num)]
  exact sEl_mem (by norm_num)

theorem fusion_J
    {ψ : Equiv.Perm (Fin 12) →* CFSG.Sporadic.Fi23.J} (hψ : Function.Injective ψ)
    (hψu : ψ (adjSwap 11 10) ∈ D23) (w : CFSG.Sporadic.Fi23.J) (hw : orderOf w = 5) :
    ∃ g : CFSG.Sporadic.Fi23.J, g * w * g⁻¹ ∈ Subgroup.zpowers (ψ cyc5) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite CFSG.Sporadic.Fi23.J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)
  have hcomm : Commute (ψ cyc5) (ψ cyc5') :=
    (show Commute cyc5 cyc5' from cyc5_comm_cyc5').map ψ
  have hx5 : ψ cyc5 ^ 5 = 1 := by rw [← map_pow, cyc5_pow_five, map_one]
  have hy5 : ψ cyc5' ^ 5 = 1 := by rw [← map_pow, cyc5'_pow_five, map_one]
  have hx1 : ψ cyc5 ≠ 1 := fun h => cyc5_ne_one (hψ (h.trans (map_one ψ).symm))
  have hyx : ∀ k < 5, ψ cyc5' ≠ ψ cyc5 ^ k := fun k hk h =>
    cyc5'_ne_pow k hk (hψ (h.trans (map_pow ψ cyc5 k).symm))
  have hQ := @CommutingPair.card_closure_pair_eq_sq (↥CFSG.Sporadic.Fi23.J) inferInstance inferInstance 5 _ _ _
    hcomm hx5 hy5 hx1 hyx (by rw [card_J]; norm_num)
  have hQfull : Nat.card (Subgroup.closure ({ψ cyc5, ψ cyc5'} : Set CFSG.Sporadic.Fi23.J)) =
      5 ^ (Nat.card (⊤ : Subgroup CFSG.Sporadic.Fi23.J)).factorization 5 := by
    rw [hQ, Subgroup.card_top, CFSG.HardMathSupport.Dickson.I271.fi23J_card_five]
  obtain ⟨g, -, hg⟩ := Co3T.exists_conj_mem_of_full le_top hQfull (Subgroup.mem_top w) hw
  have hxu : ψ cyc5 * ψ (adjSwap 11 10) = ψ (adjSwap 11 10) * ψ cyc5 := by
    rw [← map_mul, ← map_mul, adjSwap_ten_comm_cyc5]
  have hyu : ψ cyc5' * ψ (adjSwap 11 10) = ψ (adjSwap 11 10) * ψ cyc5' := by
    rw [← map_mul, ← map_mul, adjSwap_ten_comm_cyc5']
  have hQu : Subgroup.closure ({ψ cyc5, ψ cyc5'} : Set CFSG.Sporadic.Fi23.J) ≤
      Subgroup.centralizer ({ψ (adjSwap 11 10)} : Set CFSG.Sporadic.Fi23.J) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hxu
    · exact Subgroup.mem_centralizer_singleton_iff.2 hyu
  have hqu := Subgroup.mem_centralizer_singleton_iff.1 (hQu hg)
  obtain ⟨h, hh⟩ := isConj_iff.1 (show IsConj d (ψ (adjSwap 11 10)) from hψu)
  rw [← hh] at hqu hxu
  have ha := @conj_inv_mul_comm (↥CFSG.Sporadic.Fi23.J) inferInstance h (g⁻¹ * w * g) d hqu
  have hb := @conj_inv_mul_comm (↥CFSG.Sporadic.Fi23.J) inferInstance h (ψ cyc5) d hxu
  have hao : orderOf (h⁻¹ * (g⁻¹ * w * g) * h) = 5 := by
    rw [orderOf_inv_mul_mul, orderOf_inv_mul_mul, hw]
  have hbo : orderOf (h⁻¹ * ψ cyc5 * h) = 5 := by
    rw [orderOf_inv_mul_mul, orderOf_injective ψ hψ cyc5]
    exact orderOf_eq_prime cyc5_pow_five cyc5_ne_one
  obtain ⟨k, -, hk⟩ := cd_fusion ha hb hao hbo
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hk
  refine ⟨h * k * h⁻¹ * g⁻¹, Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩⟩
  calc ψ cyc5 ^ n = (h * (h⁻¹ * ψ cyc5 * h) * h⁻¹) ^ n := by group
    _ = h * (h⁻¹ * ψ cyc5 * h) ^ n * h⁻¹ := by rw [conj_zpow]
    _ = h * (k * (h⁻¹ * (g⁻¹ * w * g) * h) * k⁻¹) * h⁻¹ := by rw [hn]
    _ = h * k * h⁻¹ * g⁻¹ * w * (h * k * h⁻¹ * g⁻¹)⁻¹ := by group

end FusionJ

section Main

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

theorem card_centralizer_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (y : A) :
    Nat.card (Subgroup.centralizer ({y} : Set A)) = Nat.card (Subgroup.centralizer ({e y} : Set B)) := by
  have hmap : (Subgroup.centralizer ({y} : Set A)).map e.toMonoidHom =
      Subgroup.centralizer ({e y} : Set B) := by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [← map_mul, hu, map_mul]
    · intro hz
      refine ⟨e.symm z, ?_, by simp⟩
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz]
  rw [← hmap, Subgroup.card_map_of_injective e.injective]

variable {S : Type} [Group S] [Finite S]

theorem layer_of_facts (ψ : Equiv.Perm (Fin 12) →* S) (hψ : Function.Injective ψ)
    (hfus : ∀ w : S, orderOf w = 5 → ∃ g : S, g * w * g⁻¹ ∈ Subgroup.zpowers (ψ cyc5))
    (hcard : ∀ y : S, orderOf y = 5 → Nat.card (Subgroup.centralizer ({y} : Set S)) ≤ 25200)
    (hcore : ∀ y : S, orderOf y = 5 → GLAPPrimeCoreOf 5 (Subgroup.centralizer ({y} : Set S)) = ⊥)
    (x : S) (hx : orderOf x = 5) :
    ∃ Λ : Subgroup S, GLAPComponent 5 (Subgroup.centralizer ({x} : Set S)) Λ ∧
      (∀ H : Subgroup S, GLAPComponent 5 (Subgroup.centralizer ({x} : Set S)) H → H = Λ) ∧
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.IsAltType 7 ↥Λ ∧ x ∉ Λ := by
  obtain ⟨g, hg⟩ := hfus x hx
  set ψ' : Equiv.Perm (Fin 12) →* S := (MulAut.conj g⁻¹).toMonoidHom.comp ψ with hψ'def
  have hψ' : Function.Injective ψ' := (MulAut.conj g⁻¹).injective.comp hψ
  have hψ'c : ψ' cyc5 = g⁻¹ * ψ cyc5 * g⁻¹⁻¹ := by
    simp only [hψ'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hxmem : x ∈ Subgroup.zpowers (ψ' cyc5) := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    rw [hψ'c, conj_zpow, hn]
    group
  have hψ'o : orderOf (ψ' cyc5) = 5 := by
    rw [orderOf_injective ψ' hψ' cyc5]
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact orderOf_eq_prime cyc5_pow_five cyc5_ne_one
  have hzp : Subgroup.zpowers x = Subgroup.zpowers (ψ' cyc5) := by
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hxmem)
    rw [Nat.card_zpowers, Nat.card_zpowers, hx, hψ'o]
  exact layer_of_model ψ' hψ' hzp (hcard x hx)
    ((CFSG.HardMathSupport.Dickson.I271.glaPPrimeCoreOf_eq_bot_iff_glaPPrimeCore 5 _).1 (hcore x hx))

theorem layer_of_facts_equiv {B : Type} [instB : Group B] (e : S ≃* B) (ψ : Equiv.Perm (Fin 12) →* B)
    (hψ : Function.Injective ψ)
    (hfus : ∀ w : B, orderOf w = 5 → ∃ g : B, g * w * g⁻¹ ∈ Subgroup.zpowers (ψ cyc5))
    (hcard : ∀ y : B, orderOf y = 5 → Nat.card (Subgroup.centralizer ({y} : Set B)) ≤ 25200)
    (hcore : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt 5 B)
    (x : S) (hx : orderOf x = 5) :
    ∃ Λ : Subgroup S, GLAPComponent 5 (Subgroup.centralizer ({x} : Set S)) Λ ∧
      (∀ H : Subgroup S, GLAPComponent 5 (Subgroup.centralizer ({x} : Set S)) H → H = Λ) ∧
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.IsAltType 7 ↥Λ ∧ x ∉ Λ := by
  refine layer_of_facts (e.symm.toMonoidHom.comp ψ) (e.symm.injective.comp hψ) ?_ ?_
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt.of_mulEquiv e hcore) x hx
  · intro w hw
    have hew : orderOf (e w) = 5 := by rw [MulEquiv.orderOf_eq]; exact hw
    obtain ⟨g, hg⟩ := hfus (e w) hew
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨e.symm g, Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_zpow, hn, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  · intro y hy
    have hey : orderOf (e y) = 5 := by rw [MulEquiv.orderOf_eq]; exact hy
    rw [card_centralizer_mulEquiv e y]
    exact hcard (e y) hey

end Main

section Fi23Card

open CFSG.Sporadic.Fi23 CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem card_centralizer_five_le (y : J) (hy : orderOf y = 5) :
    Nat.card (Subgroup.centralizer ({y} : Set J)) ≤ 25200 := by
  obtain ⟨m, hm, hm21, -⟩ := Fi23Five.card_centralizer_five y hy
  rw [hm]
  omega

section Layer

theorem fi23FiveLayer_holds : Inputs2324.Fi23FiveLayer := by
  intro S _ _ hsp x hx
  obtain ⟨e₁⟩ := hsp
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv
  have e₂ : S ≃* CFSG.Blueprint.NativeSporadic.Fi23 := e₁.trans b.symm
  have e : S ≃* ↥J := e₂.trans fi23EquivJ
  obtain ⟨ψ, hψ, hψu⟩ := exists_injective_s12
  exact layer_of_facts_equiv (B := ↥J) (instB := inferInstance) e ψ hψ (fusion_J hψ hψu)
    card_centralizer_five_le Fi23Five.oPrimeCoreTrivialAt_Fi23J_five x hx

end Layer

end Fi23Card

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSpor5

end
