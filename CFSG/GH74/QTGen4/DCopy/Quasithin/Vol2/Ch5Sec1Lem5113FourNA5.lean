module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113FourNA5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113FourCZ

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

@[expose] def Stmt5_1_13_four_nA5_four_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
    L = ⁅L, thompsonJ T⁆ →
    ∀ V' : Subgroup G, IsCh5Module T L V' → quasithinOmegaOneCenter T ≤ V' →
      ⁅V', thompsonJ T⁆ ≠ ⊥ → n = 2 → IsCommCentralSplit L T V' → IsBarS5 L T V' →
      IsS5ModCh5 L T ⁅V', L⁆ →
      Nat.card ↥⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T),
        conjClosure Kh₁ T⁆ ≠ 2 ^ 4

theorem stmt5_1_13_four_nA5_of_F4 (h5171 : A5.Stmt5_1_7_one_F4) (h51 : AsB51)
    (h4 : Stmt5_1_13_four_nA5_four_F4) : Stmt5_1_13_four_nA5_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA hLJ V' hV' hZV' hJV hn2 hsplit hS5
    hmodS5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have h4' := h4 G T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA hLJ V' hV' hZV' hJV hn2 hsplit
    hS5 hmodS5
  obtain ⟨e, pk⟩ := m.exists_a7Pack_F4 h5171 h51 hc5 hmax hZ hA
  have h64 := pk.card.resolve_left h4'

  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  have hTLT : IsSylowTwoOf T (L ⊔ T) := h.isSylowTwoOf le_sup_right
  have hsyl : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hTLT le_sup_left (sup_le Subgroup.le_normalizer hTL)
  have hZT : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
    fun z hz => (mem_quasithinOmegaOneCenter_iff.mp hz).2.1
  have hBZ := borelL_le_centralizer_of_s5 h.maximal.1.2.1.2.1 h.sylow.1 hTL hsyl
    hV'.isTwoReducedIn hsplit hmodS5 hZV' hZT
  obtain ⟨-, -, D₃, hD₃, -, hD₃K, -, -⟩ := ty

  obtain ⟨β, hβ⟩ := A7ZK.exists_coreMod_equiv e pk.le_normalizer pk.elemAbelian pk.pCoreOf_le
    pk.irr pk.not_le_centralizer h64
  set u := β.symm ⟨A7ZK.v56, A7ZK.v56_mem⟩ with hu
  have hβu : (β u : G6.PermMod 7) = A7ZK.v56 := by
    rw [hu, MulEquiv.apply_symm_apply]
  have hu1 : u ≠ 1 := by
    intro h1
    apply A7ZK.v56_ne_one
    rewrite [← hβu, h1, map_one]
    rfl

  have himK : ∀ y : ↥(conjClosure Kh₁ T), (y : G) ∈ oTwoUpper H →
      e (QuotientGroup.mk y) ∈ A7Std.r0 := fun y hy => by
    rw [← pk.r0]
    exact ⟨QuotientGroup.mk y, ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩, rfl⟩
  have himT : ∀ y : ↥(conjClosure Kh₁ T), (y : G) ∈ T →
      e (QuotientGroup.mk y) ∈ A7Std.p0 := fun y hy => by
    rw [← pk.p0]
    exact ⟨QuotientGroup.mk y, ⟨y, Subgroup.mem_subgroupOf.mpr ⟨hy, y.2⟩, rfl⟩, rfl⟩

  have hfixσ : ∀ (y : ↥(conjClosure Kh₁ T)),
      G6.permAct 7 ((e (QuotientGroup.mk y) : alternatingGroup (Fin 7)) : Perm (Fin 7))
        A7ZK.v56 = A7ZK.v56 → A7ZK.conjAut pk.le_normalizer y u = u := by
    intro y hy
    apply β.injective
    apply Subtype.ext
    rw [hβ y u, hβu, hy]
  have hfixK : ∀ y : ↥(conjClosure Kh₁ T), (y : G) ∈ oTwoUpper H →
      A7ZK.conjAut pk.le_normalizer y u = u := by
    intro y hy
    refine hfixσ y (A7ZK.permAct_v56 (Or.inl ?_))
    exact (A7Std.mem_r0 _).mp (himK y hy)
  have hfixT : ∀ y : ↥(conjClosure Kh₁ T), (y : G) ∈ T →
      A7ZK.conjAut pk.le_normalizer y u = u := by
    intro y hy
    refine hfixσ y (A7ZK.permAct_v56 ?_)
    exact A7ZK.p0L_stab56 _ (A7Std.mem_p0.mp (himT y hy))

  have hyK : ∃ y : ↥(conjClosure Kh₁ T), (y : G) ∈ oTwoUpper H ∧
      e (QuotientGroup.mk y) = A7ZK.c5 := by
    have h1 : A7ZK.c5 ∈ (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)).map e.toMonoidHom :=
      pk.r0 ▸ A7ZK.c5_mem
    obtain ⟨q, ⟨y, hy, rfl⟩, hq⟩ := h1
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, hq⟩
  obtain ⟨y5, hy5K, hy5⟩ := hyK
  have hyT : ∀ x ∈ A7Std.p0, ∃ y : ↥(conjClosure Kh₁ T), (y : G) ∈ T ∧
      e (QuotientGroup.mk y) = x := by
    intro x hx
    rw [← pk.p0] at hx
    obtain ⟨q, ⟨y, hy, rfl⟩, hq⟩ := hx
    exact ⟨y, (Subgroup.mem_subgroupOf.mp hy).1, hq⟩
  obtain ⟨ya, hyaT, hya⟩ := hyT _ A7ZK.eval7_p0aWord_mem
  have hya' : ((e (QuotientGroup.mk ya) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      A7Std.p0a := by
    rw [hya]
    exact Equiv.ext A7ZK.eval7_p0aWord

  have hone : ∀ u' : ↥⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T),
      conjClosure Kh₁ T⁆, A7ZK.conjAut pk.le_normalizer y5 u' = u' →
      A7ZK.conjAut pk.le_normalizer ya u' = u' → u' = 1 ∨ u' = u := by
    intro u' h5 ha
    have k5 := hβ y5 u'
    have ka := hβ ya u'
    rw [h5, hy5] at k5
    rw [ha, hya'] at ka
    rcases A7ZK.eq_one_or_eq_v56 (G6.mem_coreMod.mp (β u').2) k5.symm ka.symm with
      h1 | h1
    · left
      apply β.injective
      rw [map_one]
      exact Subtype.ext h1
    · right
      apply β.injective
      exact Subtype.ext (h1.trans hβu.symm)

  have hTu : ∀ t ∈ T, t * (u : G) * t⁻¹ = u := by
    intro t ht
    have htU : t * (u : G) * t⁻¹ ∈ ⁅conjClosure (quasithinOmegaOneCenter T)
        (conjClosure Kh₁ T ⊔ T), conjClosure Kh₁ T⁆ :=
      (Subgroup.mem_normalizer_iff.mp (pk.T_le_normalizer ht) u).mp u.2

    have hc : ∀ y : ↥(conjClosure Kh₁ T), ∀ hy' : (t⁻¹ * y * t : G) ∈ conjClosure Kh₁ T,
        A7ZK.conjAut pk.le_normalizer ⟨t⁻¹ * y * t, hy'⟩ u = u →
        A7ZK.conjAut pk.le_normalizer y ⟨_, htU⟩ = ⟨_, htU⟩ := by
      intro y hy' hfix
      have h1 : (t⁻¹ * y * t) * (u : G) * (t⁻¹ * y * t)⁻¹ = u := congrArg Subtype.val hfix
      apply Subtype.ext
      rw [A7ZK.coe_conjAut]
      show (y : G) * (t * u * t⁻¹) * (y : G)⁻¹ = t * u * t⁻¹
      calc (y : G) * (t * u * t⁻¹) * (y : G)⁻¹ =
            t * ((t⁻¹ * y * t) * u * (t⁻¹ * y * t)⁻¹) * t⁻¹ := by group
        _ = t * u * t⁻¹ := by rw [h1]
    have hTK' : ∀ y : G, y ∈ conjClosure Kh₁ T → t⁻¹ * y * t ∈ conjClosure Kh₁ T := fun y hy => by
      have h1 := (Subgroup.mem_normalizer_iff.mp (pk.T_le (T.inv_mem ht)) y).mp hy
      simpa using h1
    have h5 : A7ZK.conjAut pk.le_normalizer y5 ⟨_, htU⟩ = ⟨_, htU⟩ := by
      refine hc y5 (hTK' _ y5.2) (hfixK _ ?_)
      have h1 := (Subgroup.mem_normalizer_iff.mp (pk.T_le_K (T.inv_mem ht)) _).mp hy5K
      simpa using h1
    have ha : A7ZK.conjAut pk.le_normalizer ya ⟨_, htU⟩ = ⟨_, htU⟩ := by
      refine hc ya (hTK' _ ya.2) (hfixT _ ?_)
      exact T.mul_mem (T.mul_mem (T.inv_mem ht) hyaT) ht
    rcases hone _ h5 ha with h1 | h1
    · exfalso
      apply hu1
      have h2 : t * (u : G) * t⁻¹ = 1 := congrArg Subtype.val h1
      apply Subtype.ext
      have h3 : (u : G) = t⁻¹ * (t * u * t⁻¹) * t := by group
      rw [h3, h2]
      simp
    · exact congrArg Subtype.val h1
  have huZ : (u : G) ∈ quasithinOmegaOneCenter T :=
    mem_quasithinOmegaOneCenter_iff.mpr ⟨pk.le_T (pk.U_le u.2),
      Subgroup.mem_centralizer_iff.mpr fun t ht => by
        calc t * (u : G) = t * u * t⁻¹ * t := by group
          _ = u * t := by rw [hTu t ht],
      pk.elemAbelian.2 _ u.2⟩

  have hON : pCoreOf 2 (conjClosure Kh₁ T) ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    refine le_trans ?_ ((F7.isSylowTwoOf_pCoreOf_le pk.sylow).trans pk.T_le_K)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
        (pk.T_le.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hconj : ∀ d ∈ D₃, ∀ k ∈ oTwoUpper H, d * k * d⁻¹ ∈ oTwoUpper H := by
    intro d hd k hk
    have hdKh : d ∈ conjClosure Kh₁ T := (hD₃ hd).2
    have hdZ := hBZ (m.nota.2.1.1 (hD₃ hd).1)

    have hdu : A7ZK.conjAut pk.le_normalizer ⟨d, hdKh⟩ u = u := by
      apply Subtype.ext
      rw [A7ZK.coe_conjAut]
      have h1 : (u : G) * d = d * u := Subgroup.mem_centralizer_iff.mp hdZ _ huZ
      show d * (u : G) * d⁻¹ = u
      rw [← h1, mul_inv_cancel_right]
    have hσ : G6.permAct 7 ((e (QuotientGroup.mk ⟨d, hdKh⟩) : alternatingGroup (Fin 7)) :
        Perm (Fin 7)) A7ZK.v56 = A7ZK.v56 := by
      have h1 := hβ ⟨d, hdKh⟩ u
      rw [hdu, hβu] at h1
      exact h1.symm
    refine mem_of_conj_mem_modO2Image pk.K_le
      (by rw [m.closure]; exact A3.conjClosure_perfect m.comp.2.1) hON hdKh ?_ hk
    intro k' hk'
    have hr : e (QuotientGroup.mk k') ∈ A7Std.r0 := by
      rw [← pk.r0]
      exact ⟨_, hk', rfl⟩
    have h1 := A7ZK.mem_r0_of_permAct_v56 hσ hr
    rw [← map_inv, ← map_mul, ← map_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, ← pk.r0] at h1
    obtain ⟨x, hx, hxe⟩ := h1
    rw [show x = _ from e.injective hxe] at hx
    exact hx
  apply hD₃K
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · exact hconj d hd k
  · intro hk
    have h1 := hconj d⁻¹ (D₃.inv_mem hd) _ hk
    simpa [mul_assoc] using h1

end CFSG.Quasithin.H13
