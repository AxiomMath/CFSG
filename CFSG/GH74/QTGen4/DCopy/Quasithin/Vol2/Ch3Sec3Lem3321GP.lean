module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Stmt3313LT
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321GP

public section
namespace CFSG.Quasithin.H13.L3321

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Lift CFSG.Quasithin.S152N
open CFSG.Open (pCoreOf)

section Inner

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G} {α : ↥L →* SL4}

theorem exists_inner_F4 (h13 : Stmt3_3_13LT_F4) (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) (hU : ((T ⊓ L).subgroupOf L).map α = FLc.Ut 4)
    (hout : ¬ InducesInnerOn T L) :
    ∃ S : Subgroup G, S ≤ T ∧ T ≤ Subgroup.normalizer (S : Set G) ∧ T ⊓ L ≤ S ∧
      pCoreOf 2 (L ⊔ T) ≤ S ∧
      (∀ s ∈ S, ∃ y : ↥L, α y ∈ FLc.Ut 4 ∧ ∀ (x : ↥L) (hx : s * (x : G) * s⁻¹ ∈ L),
        α ⟨s * x * s⁻¹, hx⟩ = α y * α x * (α y)⁻¹) ∧
      (∃ t₀ ∈ T, t₀ ∉ S ∧ ∃ u ∈ FLc.Ut 4, (∀ (x : ↥L) (hx : t₀ * (x : G) * t₀⁻¹ ∈ L),
        α ⟨t₀ * x * t₀⁻¹, hx⟩ = u * gam (α x) * u⁻¹) ∧ ∀ x ∈ T, x ∈ S ∨ x * t₀⁻¹ ∈ S) ∧
      D ≤ Subgroup.normalizer (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := h.sylow.1
  obtain ⟨ψ, -, hψk, hψe⟩ := exists_psiH hα hker hTL hT2 hU hout
  have hTH : T ≤ L3316.liftPre α P2 ⊔ T := le_sup_right
  have hψT : ∀ t (ht : t ∈ T), ∃ (u : SL4) (hu : u ∈ FLc.Ut 4) (k : Multiplicative (ZMod 2)),
      indAut hα hker ⟨t, hTL ht⟩ = xiHom ⟨⟨u, Ut_le_P2 hu⟩, k⟩ ∧
        ψ ⟨t, hTH ht⟩ = chiHom ⟨⟨u, Ut_le_P2 hu⟩, k⟩ := by
    intro t ht
    obtain ⟨u, hu, k, hk⟩ := exists_xiHom_of_map_Ut _ (map_Ut_indAut hα hker hTL hU ht)
    exact ⟨u, hu, k, hk, hψe t (hTH ht) (hTL ht) _ hk⟩
  have hψL : ∀ l : ↥L, ∀ (hlP : α l ∈ P2) (hlH : (l : G) ∈ L3316.liftPre α P2 ⊔ T),
      ψ ⟨l, hlH⟩ = chiHom ⟨⟨α l, hlP⟩, 1⟩ := by
    intro l hlP hlH
    refine hψe l hlH (Subgroup.le_normalizer l.2) _ ?_
    rw [indAut_of_mem, xiHom_mk, map_one, mul_one]
  set S : Subgroup G := T ⊓ ((RegularWreathProduct.rightHom.ker.comap ψ).map
    (L3316.liftPre α P2 ⊔ T).subtype) with hS
  have hmemS : ∀ x (hx : x ∈ T), x ∈ S ↔ (ψ ⟨x, hTH hx⟩).right = 1 := by
    intro x hx
    constructor
    · rintro ⟨-, ⟨y, hy, rfl⟩⟩
      have hy' : ψ y ∈ RegularWreathProduct.rightHom.ker := hy
      rw [MonoidHom.mem_ker, RegularWreathProduct.rightHom_eq_right] at hy'
      exact hy'
    · intro h1
      refine ⟨hx, ⟨x, hTH hx⟩, ?_, rfl⟩
      show ψ ⟨x, hTH hx⟩ ∈ RegularWreathProduct.rightHom.ker
      rw [MonoidHom.mem_ker, RegularWreathProduct.rightHom_eq_right]
      exact h1
  have hST : S ≤ T := inf_le_left
  have hTS : T ≤ Subgroup.normalizer (S : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ y (hy : y ∈ T), (ψ ⟨t * y * t⁻¹, hTH (T.mul_mem (T.mul_mem ht hy)
        (T.inv_mem ht))⟩).right = (ψ ⟨y, hTH hy⟩).right := by
      intro y hy
      have e : (⟨t * y * t⁻¹, hTH (T.mul_mem (T.mul_mem ht hy) (T.inv_mem ht))⟩ :
          ↥(L3316.liftPre α P2 ⊔ T)) =
          ⟨t, hTH ht⟩ * ⟨y, hTH hy⟩ * (⟨t, hTH ht⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, RegularWreathProduct.mul_right,
        RegularWreathProduct.mul_right, RegularWreathProduct.inv_right, mul_comm,
        ← mul_assoc, inv_mul_cancel, one_mul]
    constructor
    · intro hx
      have hxT := hST hx
      have hy := T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht)
      rw [hmemS _ hy, key x hxT]
      exact (hmemS x hxT).1 hx
    · intro hx
      have hy := hST hx
      have hxT : x ∈ T := by
        have := T.mul_mem (T.mul_mem (T.inv_mem ht) hy) ht
        simpa [mul_assoc] using this
      rw [hmemS x hxT, ← key x hxT]
      exact (hmemS _ hy).1 hx
  have hTLS : T ⊓ L ≤ S := by
    intro x hx
    rw [hmemS x hx.1, hψL ⟨x, hx.2⟩ (Ut_le_P2 (by rw [← hU]; exact ⟨⟨x, hx.2⟩,
      Subgroup.mem_subgroupOf.2 hx, rfl⟩)) (hTH hx.1), chiHom_right]
  have hQS : pCoreOf 2 (L ⊔ T) ≤ S := by
    intro q hq
    have hqT : q ∈ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf hq
    have hind : indAut hα hker ⟨q, hTL hqT⟩ = xiHom 1 := by
      rw [map_one]
      refine MulEquiv.ext fun y => ?_
      obtain ⟨l, rfl⟩ := hα y
      rw [indAut_apply, MulAut.one_apply]
      have hx := (Subgroup.mem_normalizer_iff.mp (hTL hqT) l).mp l.2
      have h1 : (⟨q * l * q⁻¹, hx⟩ : ↥L) * l⁻¹ ∈ CFSG.pCore 2 ↥L := by
        rw [Lem3328.mem_pCore_iff]
        refine inf_le_pCoreOf (T := T) ⟨?_, L.mul_mem hx (L.inv_mem l.2)⟩
        have hql : q * (l : G) * q⁻¹ * (l : G)⁻¹ = q * ((l : G) * q⁻¹ * (l : G)⁻¹) := by group
        show q * (l : G) * q⁻¹ * (l : G)⁻¹ ∈ pCoreOf 2 (L ⊔ T)
        rw [hql]
        refine Subgroup.mul_mem _ hq ?_
        have := (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
          (L ⊔ T) (Subgroup.mem_sup_left l.2)) q⁻¹).mp (Subgroup.inv_mem _ hq)
        exact this
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1
    rw [hmemS q hqT, hψe q (hTH hqT) (hTL hqT) _ hind, map_one]
    rfl
  have hconj : ∀ s ∈ S, ∃ y : ↥L, α y ∈ FLc.Ut 4 ∧ ∀ (x : ↥L) (hx : s * (x : G) * s⁻¹ ∈ L),
      α ⟨s * x * s⁻¹, hx⟩ = α y * α x * (α y)⁻¹ := by
    intro s hs
    obtain ⟨u, hu, k, hk, hψ⟩ := hψT s (hST hs)
    have hk1 : k = 1 := by
      have := (hmemS s (hST hs)).1 hs
      rwa [hψ, chiHom_right] at this
    subst hk1
    rw [xiHom_mk, map_one, mul_one] at hk
    obtain ⟨y, hy⟩ := hα u
    refine ⟨y, by rw [hy]; exact hu, fun x hx => ?_⟩
    have h2 := indAut_apply hα hker ⟨s, hTL (hST hs)⟩ x
    rw [hk, MulAut.conj_apply] at h2
    rw [hy]
    exact h2.symm
  have hout' : ∃ (t₀ : G) (ht₀ : t₀ ∈ T) (u : SL4) (hu : u ∈ FLc.Ut 4),
      indAut hα hker ⟨t₀, hTL ht₀⟩ = xiHom ⟨⟨u, Ut_le_P2 hu⟩, Multiplicative.ofAdd 1⟩ := by
    by_contra hno
    apply hout
    intro t ht
    obtain ⟨u, hu, k, hk, -⟩ := hψT t ht
    rcases mult_z2_cases k with rfl | rfl
    · rw [xiHom_mk, map_one, mul_one] at hk
      obtain ⟨y, hy⟩ := hα u
      refine ⟨y, y.2, fun x hx => ?_⟩
      have hxt := (Subgroup.mem_normalizer_iff.mp (hTL ht) x).mp hx
      have h1 : α ⟨t * x * t⁻¹, hxt⟩ = α (y * ⟨x, hx⟩ * y⁻¹) := by
        have h2 := indAut_apply hα hker ⟨t, hTL ht⟩ ⟨x, hx⟩
        rw [hk, MulAut.conj_apply] at h2
        rw [map_mul, map_mul, map_inv, hy]
        exact h2.symm
      have h3 : (⟨t * x * t⁻¹, hxt⟩ : ↥L) * (y * ⟨x, hx⟩ * y⁻¹)⁻¹ ∈ CFSG.pCore 2 ↥L := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
      exact (Lem3328.mem_pCore_iff _).1 h3
    · exact absurd ⟨t, ht, u, hu, hk⟩ hno
  obtain ⟨t₀, ht₀, u₀, hu₀, hk₀⟩ := hout'
  have hψt₀ : (ψ ⟨t₀, hTH ht₀⟩).right = Multiplicative.ofAdd 1 := by
    rw [hψe t₀ (hTH ht₀) (hTL ht₀) _ hk₀, chiHom_right]
  have hact : ∀ (x : ↥L) (hx : t₀ * (x : G) * t₀⁻¹ ∈ L),
      α ⟨t₀ * x * t₀⁻¹, hx⟩ = u₀ * gam (α x) * u₀⁻¹ := by
    intro x hx
    have h2 := indAut_apply hα hker ⟨t₀, hTL ht₀⟩ x
    rw [hk₀, xiHom_mk, homZ2_one'] at h2
    exact h2.symm
  have hdich : ∀ x ∈ T, x ∈ S ∨ x * t₀⁻¹ ∈ S := by
    intro x hx
    rcases mult_z2_cases (ψ ⟨x, hTH hx⟩).right with h1 | h1
    · exact Or.inl ((hmemS x hx).2 h1)
    · right
      have hy := T.mul_mem hx (T.inv_mem ht₀)
      rw [hmemS _ hy]
      have e : (⟨x * t₀⁻¹, hTH hy⟩ : ↥(L3316.liftPre α P2 ⊔ T)) =
          ⟨x, hTH hx⟩ * (⟨t₀, hTH ht₀⟩)⁻¹ := rfl
      rw [e, map_mul, map_inv, RegularWreathProduct.mul_right, RegularWreathProduct.inv_right,
        h1, hψt₀, mul_inv_cancel]
  have hInH : InH T (L3316.liftPre α P2 ⊔ T) := by
    refine ⟨le_sup_right, fun hbot => h.toSetup331.pCoreOf_ne_bot ?_⟩
    have hOT : pCoreOf 2 (L ⊔ T) ≤ T :=
      EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
    have hle : pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 (L3316.liftPre α P2 ⊔ T) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right)
        ((sup_le_sup_right (L3316.liftPre_le α P2) T).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T))
    rw [hbot] at hle
    exact le_bot_iff.1 hle
  have hDH := h13 G T M L D _ h hInH (sup_le_sup_right (L3316.liftPre_le α P2) T)
    (nonempty_wreath hα hker hTL hT2 hU hout)
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : ↥L, (s₁ : G) ∈ T ∧ α s₁ = diagSL trN 1 := by
    have h1 : diagSL trN 1 ∈ ((T ⊓ L).subgroupOf L).map α := by
      rw [hU]
      exact diagSL_trN_mem
    obtain ⟨s, hs, hse⟩ := h1
    exact ⟨s, (Subgroup.mem_subgroupOf.1 hs).1, hse⟩
  have hψs₁ : ψ ⟨s₁, hTH hs₁.1⟩ = W3D.sW tau0 := by
    rw [hψL s₁ (by rw [hs₁.2]; exact diagSL_mem trN 1) (hTH hs₁.1)]
    have e : (⟨α s₁, by rw [hs₁.2]; exact diagSL_mem trN 1⟩ : ↥P2) =
        ⟨diagSL trN 1, diagSL_mem trN 1⟩ := Subtype.ext hs₁.2
    rw [e, chiHom_diagSL]
  have key : ∀ d ∈ D, ∀ x ∈ S, d * x * d⁻¹ ∈ S := by
    intro d hd x hx
    have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hd
    have hdO : d ∈ Subgroup.normalizer (pCoreOf 2 (L3316.liftPre α P2 ⊔ T) : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hDH hd)
    have hodd : Odd (orderOf d) := by
      have h1 : orderOf (⟨d, hd⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat h.Dodd h1
    have hσm : conjEnd d hdT ^ orderOf d = 1 := by
      refine DFunLike.ext (F := Monoid.End ↥T) _ _ fun y => Subtype.ext ?_
      rw [conjEnd_pow, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
      rfl
    have hσ : ∀ y : ↥T, (ψ.comp (Subgroup.inclusion hTH)) y = 1 →
        (ψ.comp (Subgroup.inclusion hTH)) (conjEnd d hdT y) = 1 := by
      intro y hy
      have h1 : Subgroup.inclusion hTH y ∈ CFSG.pCore 2 ↥(L3316.liftPre α P2 ⊔ T) := by
        rw [← hψk]
        exact hy
      have h2 := (Lem3328.mem_pCore_iff _).1 h1
      have h3 : d * (y : G) * d⁻¹ ∈ pCoreOf 2 (L3316.liftPre α P2 ⊔ T) :=
        (Subgroup.mem_normalizer_iff.mp hdO _).mp h2
      have h4 : Subgroup.inclusion hTH (conjEnd d hdT y) ∈
          CFSG.pCore 2 ↥(L3316.liftPre α P2 ⊔ T) := (Lem3328.mem_pCore_iff _).2 h3
      rw [← hψk] at h4
      exact h4
    have h1 := W3D.right_map_eq_one (ψ.comp (Subgroup.inclusion hTH)) (conjEnd d hdT)
      tau0_mul_self tau0_ne_one (fun y q => by
        obtain ⟨u, hu, k, -, hψu⟩ := hψT y y.2
        show (ψ ⟨y, hTH y.2⟩).left q = 1 ∨ (ψ ⟨y, hTH y.2⟩).left q = tau0
        rw [hψu]
        exact chiHom_left_mem hu k q) (s₁ := ⟨s₁, hs₁.1⟩) (t₀ := ⟨t₀, ht₀⟩) hψs₁ hψt₀ hσ hodd hσm
      (x := ⟨x, hST hx⟩) ((hmemS x (hST hx)).1 hx)
    exact (hmemS _ ((Subgroup.mem_normalizer_iff.mp hdT x).mp (hST hx))).2 h1
  have hDS : D ≤ Subgroup.normalizer (S : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact key d hd x
    · intro hx
      have h1 := key d⁻¹ (D.inv_mem hd) _ hx
      simpa [mul_assoc] using h1
  have ht₀S : t₀ ∉ S := fun h1 => W3D.ofAdd_one_ne (hψt₀.symm.trans ((hmemS t₀ ht₀).1 h1))
  exact ⟨S, hST, hTS, hTLS, hQS, hconj, ⟨t₀, ht₀, ht₀S, u₀, hu₀, hact, hdich⟩, hDS⟩

end Inner

end CFSG.Quasithin.H13.L3321
