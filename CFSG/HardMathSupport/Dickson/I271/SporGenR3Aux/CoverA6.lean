module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SplitA6

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.Yardstones.Md0ec50421ce4

section Defs

@[expose] def A6Split3 {Q : Type} [Group Q] (L : Subgroup Q) : Prop :=
  Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∧
    ∃ (t e₁ e₂ : Q) (E : Subgroup Q) (a b c d : ℕ),
      t ∈ Subgroup.normalizer (L : Set Q) ∧ E ≤ L ∧ Nat.card ↥E = 9 ∧ e₁ ∈ E ∧ e₂ ∈ E ∧
      e₁ * e₂ = e₂ * e₁ ∧ (∀ g ∈ E, ∃ i j : ℕ, g = e₁ ^ i * e₂ ^ j) ∧
      t * e₁ * t⁻¹ = e₁ ^ a * e₂ ^ b ∧ t * e₂ * t⁻¹ = e₁ ^ c * e₂ ^ d ∧
      a * d ≡ b * c + 2 [MOD 3]

@[expose] def SplitGoodAt (p : ℕ) {Q : Type} [Group Q] (J : Subgroup Q) : Prop :=
  LeafType p (PSimple p J) ∨ (IsA6At p (PSimple p J) ∧ A6Split3 J)

@[expose] def CentShapeSplit (p : ℕ) (Q : Type) [Group Q] : Prop :=
  ∀ k : Q, k ≠ 1 → k ^ p = 1 →
    PConstrainedShape p (Subgroup.centralizer ({k} : Set Q)) ∨
      ∃ J : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) J ∧
        (∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I → I = J) ∧
        SplitGoodAt p J

@[expose] def RkTriv3 (T : Type) [Group T] : Prop :=
  Nonempty ((T ⧸ Subgroup.center T) ≃* alternatingGroup (Fin 6)) → Subgroup.center T = ⊥

theorem RkTriv3.of_equiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T') (h : RkTriv3 T) :
    RkTriv3 T' := by
  rintro ⟨f⟩
  have eq : (T ⧸ Subgroup.center T) ≃* (T' ⧸ Subgroup.center T') :=
    QuotientGroup.congr (Subgroup.center T) (Subgroup.center T') e (Subgroup.map_center_eq e)
  have h1 := h ⟨eq.trans f⟩
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have : e.symm z ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_center_iff.1 hz (e g)
    apply e.injective
    simpa using this
  rw [h1, Subgroup.mem_bot] at this
  simpa using congrArg e this

end Defs

section Transport

variable {Q Q' : Type} [Group Q] [Group Q']

theorem A6Split3.map (e : Q ≃* Q') {L : Subgroup Q} (h : A6Split3 L) :
    A6Split3 (L.map e.toMonoidHom) := by
  obtain ⟨⟨eL⟩, t, e₁, e₂, E, a, b, c, d, ht, hEL, hE, he₁, he₂, hcomm, hgen, h1, h2, hdet⟩ := h
  refine ⟨⟨(e.subgroupMap L).symm.trans eL⟩, e t, e e₁, e e₂, E.map e.toMonoidHom, a, b, c, d,
    ?_, Subgroup.map_mono hEL, ?_, Subgroup.mem_map_of_mem _ he₁, Subgroup.mem_map_of_mem _ he₂,
    ?_, ?_, ?_, ?_, hdet⟩
  · rw [Subgroup.mem_normalizer_iff] at ht ⊢
    intro g'
    obtain ⟨g, rfl⟩ := e.surjective g'
    have hmem : ∀ y : Q, e y ∈ L.map e.toMonoidHom ↔ y ∈ L := fun y =>
      Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective
    rw [hmem g, ← map_inv, ← map_mul, ← map_mul, hmem]
    exact ht g
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hE
  · rw [← map_mul, ← map_mul, hcomm]
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, j, rfl⟩ := hgen g hg
    exact ⟨i, j, by simp⟩
  · simpa using congrArg e h1
  · simpa using congrArg e h2

variable [Finite Q] [Finite Q']

theorem SplitGoodAt.of_equiv {p : ℕ} (e : Q ≃* Q') {J : Subgroup Q} (h : SplitGoodAt p J) :
    SplitGoodAt p (J.map e.toMonoidHom) := by
  have f : PSimple p J ≃* PSimple p (J.map e.toMonoidHom) :=
    pSimpleEquiv p (e.subgroupMap J)
  rcases h with hl | ⟨⟨hp3, ⟨g⟩⟩, hs⟩
  · exact Or.inl (LeafType.of_equiv f hl)
  · exact Or.inr ⟨⟨hp3, ⟨f.symm.trans g⟩⟩, hs.map e⟩

theorem CentShapeSplit.of_equiv {p : ℕ} (hp : p.Prime) (e : Q ≃* Q')
    (h : CentShapeSplit p Q) : CentShapeSplit p Q' := by
  intro k' hk1 hkp
  set k : Q := e.symm k' with hk
  have hk1' : k ≠ 1 := fun h1 => hk1 (by simpa [hk] using congrArg e h1)
  have hkp' : k ^ p = 1 := by
    apply e.injective
    simpa [hk] using hkp
  have hek : e k = k' := by simp [hk]
  have hmap : (Subgroup.centralizer ({k} : Set Q)).map e.toMonoidHom =
      Subgroup.centralizer ({k'} : Set Q') := by
    rw [map_centralizer_singleton e k, hek]
  rcases h k hk1' hkp' with hc | ⟨J, hJ, hu, hG⟩
  · left
    rw [← hmap]
    exact pConstrainedShape_map e hc
  · right
    refine ⟨J.map e.toMonoidHom, ?_, ?_, hG.of_equiv e⟩
    · rw [← hmap]
      exact glaPComponent_map_equiv hp e hJ
    · intro I' hI'
      have h1 := glaPComponent_map_equiv hp e.symm hI'
      have hmap' : (Subgroup.centralizer ({k'} : Set Q')).map e.symm.toMonoidHom =
          Subgroup.centralizer ({k} : Set Q) := by
        rw [map_centralizer_singleton e.symm k']
      rw [hmap'] at h1
      have h2 := hu _ h1
      rw [← h2, Subgroup.map_map]
      have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by ext; simp
      rw [this, Subgroup.map_id]

end Transport

section Lift

@[expose] noncomputable def conjAutOfMap {K : Type*} [Group K] (J : Subgroup K) (t : K)
    (h : J.map (MulAut.conj t).toMonoidHom = J) : MulAut ↥J :=
  (MulEquiv.subgroupMap (MulAut.conj t) J).trans (MulEquiv.subgroupCongr h)

theorem center_lift_eq_bot {K' Q : Type} [Group K'] [Finite K']
    [Group Q] (π : K' →* Q) (hker : π.ker ≤ Subgroup.center K') (hπ : Function.Surjective π)
    (hZp : IsPGroup 3 (Subgroup.center K')) {J : Subgroup K'} (hJ : ⁅J, J⁆ = J)
    (hsplit : A6Split3 (J.map π)) : Subgroup.center ↥J = ⊥ := by
  obtain ⟨⟨eL⟩, t, e₁, e₂, E, a, b, c, d, ht, hEL, hE, he₁, he₂, hcomm, hgen, h1, h2, hdet⟩ :=
    hsplit
  set L : Subgroup Q := J.map π with hL
  haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hJ
  let q : ↥J →* ↥L := π.subgroupMap J
  have hq : Function.Surjective q := MonoidHom.subgroupMap_surjective π J
  have hqker : q.ker ≤ Subgroup.center ↥J := by
    intro x hx
    have h1 : (x : K') ∈ π.ker := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 := hker h1
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 h2 (g : K'))
  have hcenL : Subgroup.center ↥L = ⊥ := center_eq_bot_of_equiv_alt6 eL
  have hZJK : ∀ z ∈ Subgroup.center ↥J, (z : K') ∈ Subgroup.center K' := by
    intro z hz
    have hqz : q z ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨u, rfl⟩ := hq g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz u]
    rw [hcenL, Subgroup.mem_bot] at hqz
    exact hker (congrArg Subtype.val hqz : π (z : K') = 1)
  have hZJ : IsPGroup 3 (Subgroup.center ↥J) := by
    intro z
    obtain ⟨n, hn⟩ := hZp ⟨(z : ↥J).1, hZJK z z.2⟩
    exact ⟨n, Subtype.ext (Subtype.ext (congrArg (fun w : Subgroup.center K' => (w : K')) hn))⟩
  obtain ⟨t', ht'⟩ := hπ t
  have hLt : ∀ g : Q, g ∈ L ↔ t * g * t⁻¹ ∈ L := Subgroup.mem_normalizer_iff.1 ht
  have hconj : J.map (MulAut.conj t').toMonoidHom = J := by
    have hperf2 : ⁅J.map (MulAut.conj t').toMonoidHom, J.map (MulAut.conj t').toMonoidHom⁆ =
        J.map (MulAut.conj t').toMonoidHom := by
      rw [← Subgroup.map_commutator, hJ]
    refine eq_of_map_eq_of_perfect π hker hperf2 hJ ?_
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have : π ((MulAut.conj t').toMonoidHom x) = t * π x * t⁻¹ := by
        simp [MulAut.conj_apply, ht']
      rw [this]
      exact (hLt (π x)).1 ⟨x, hx, rfl⟩
    · intro hy
      have hyL : y ∈ L := hy
      have hg : t⁻¹ * y * t ∈ L := by
        rw [hLt (t⁻¹ * y * t)]
        have : t * (t⁻¹ * y * t) * t⁻¹ = y := by group
        rw [this]
        exact hyL
      obtain ⟨x, hx, hxg⟩ := hg
      refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
      have : π ((MulAut.conj t').toMonoidHom x) = t * π x * t⁻¹ := by
        simp [MulAut.conj_apply, ht']
      rw [this, hxg]
      group
  let τ : MulAut ↥J := conjAutOfMap J t' hconj
  have hτZ : ∀ z ∈ Subgroup.center ↥J, τ z = z := by
    intro z hz
    apply Subtype.ext
    show t' * (z : K') * t'⁻¹ = (z : K')
    rw [Subgroup.mem_center_iff.1 (hZJK z hz) t']
    group
  have he₁L : e₁ ∈ L := hEL he₁
  have he₂L : e₂ ∈ L := hEL he₂
  obtain ⟨x, hx, hxe⟩ := he₁L
  obtain ⟨y, hy, hye⟩ := he₂L
  have hqx : (q ⟨x, hx⟩ : Q) = e₁ := hxe
  have hqy : (q ⟨y, hy⟩ : Q) = e₂ := hye
  have hEL' : E.subgroupOf L ≤ ⊤ := le_top
  refine center_eq_bot_of_det hZJ q hq hqker eL τ hτZ (E.subgroupOf L)
    (by rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv] at hE; exact hE)
    ⟨x, hx⟩ ⟨y, hy⟩ ?_ ?_ a b c d ?_ ?_ hdet
  · intro g hg
    obtain ⟨i, j, hij⟩ := hgen (g : Q) hg
    refine ⟨i, j, Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, hqx, hqy]
    exact hij
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hqx, hqy]
    exact hcomm
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, hqx, hqy]
    show π (t' * x * t'⁻¹) = _
    rw [map_mul, map_mul, map_inv, ht', hxe]
    exact h1
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, hqx, hqy]
    show π (t' * y * t'⁻¹) = _
    rw [map_mul, map_mul, map_inv, ht', hye]
    exact h2

end Lift

section Good

theorem LeafType.not_nonempty_alt6 {p : ℕ} {T : Type} [Group T] (h : LeafType p T) :
    ¬ Nonempty (T ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨f⟩
  rcases h with ⟨-, -, h3⟩ | ⟨n, hn, hn6, hpn, ⟨g⟩⟩
  · exact h3 ⟨f⟩
  · haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    have hcard : Nat.card (alternatingGroup (Fin n)) = Nat.card (alternatingGroup (Fin 6)) :=
      Nat.card_congr (g.symm.trans f).toEquiv
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_alternatingGroup,
      card_alternatingGroup] at hcard
    simp only [Fintype.card_fin] at hcard
    have h6 : (6 : ℕ).factorial = 720 := by decide
    have hn2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h62 : 2 ∣ (6 : ℕ).factorial := by rw [h6]; norm_num
    have hfact : n.factorial = (6 : ℕ).factorial := by omega
    exact hn6 ((Nat.factorial_inj (by omega : 1 < n)).1 hfact)

theorem strong_goodA6 (hChev : ChevStrong 3) {Y : Type} [Group Y]
    [Finite Y] {J B : Subgroup Y} (h : CompHyp 3 J B)
    (hG : GoodSpor 3 [] (↥J ⧸ Subgroup.center ↥J)) (hR : RkTriv3 ↥J) :
    IsStronglyBalancedIn 3 B J := by
  rcases hG with hL | ⟨-, ⟨e⟩⟩ | ⟨S, hS, -⟩
  · exact strong_leaf hChev h hL
  · have hZ := hR ⟨e⟩
    rcases Amb.a6Case h.core h.comp h.scp h.norm e with h1 | ⟨⟨-, h3, -⟩, -⟩
    · exact h1
    · rw [hZ] at h3
      simp at h3
  · simp at hS

end Good

section CoverDichSplit

variable {X : Type} [Group X] [Finite X]

theorem comp_dichotomy_coverSplit
    {K : Subgroup X} (hZp : IsPGroup 3 (Subgroup.center ↥K))
    (hOall : OPrimeCoreTrivialAt 3 (↥K ⧸ Subgroup.center ↥K))
    (hshape : CentShapeSplit 3 (↥K ⧸ Subgroup.center ↥K))
    {a k : X} (hk : k ∈ K) (hc : k⁻¹ * a ∈ Subgroup.centralizer (K : Set X))
    (hkZ : (⟨k, hk⟩ : ↥K) ∉ Subgroup.center ↥K)
    (hkp : (⟨k, hk⟩ : ↥K) ^ 3 ∈ Subgroup.center ↥K) :
    (∀ J : Subgroup X, ¬ GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J) ∨
      ∃ J₀ : Subgroup X, J₀ ≤ K ∧
        (∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
          J = J₀) ∧
        GoodSpor 3 [] (PSimple 3 (J₀.subgroupOf K)) ∧ RkTriv3 (PQuot 3 (J₀.subgroupOf K)) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (3 : ℕ).Prime := ⟨hp⟩
  set k' : ↥K := ⟨k, hk⟩ with hk'
  set π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hπdef
  have hker : π.ker ≤ Subgroup.center ↥K := (QuotientGroup.ker_mk' _).le
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  set α : MulAut ↥K := MulAut.conj k' with hα
  set β : MulAut (↥K ⧸ Subgroup.center ↥K) := MulAut.conj (π k') with hβ
  have hαβ : ∀ x, π (α x) = β (π x) := by
    intro x
    simp [hα, hβ, MulAut.conj_apply]
  have hfixα : fixSubgroup α = Subgroup.centralizer ({k'} : Set ↥K) := fixSubgroup_conj_eq k'
  have hfixβ : fixSubgroup β = Subgroup.centralizer ({π k'} : Set (↥K ⧸ Subgroup.center ↥K)) :=
    fixSubgroup_conj_eq (π k')
  have hbar1 : π k' ≠ 1 := fun h => hkZ ((QuotientGroup.eq_one_iff _).1 h)
  have hbarp : (π k') ^ 3 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hkp
  have hO : GLAPPrimeCoreOf 3 (fixSubgroup β) = ⊥ := by
    rw [hfixβ]
    exact hOall (π k') (orderOf_eq_prime hbarp hbar1)
  have hJsub : ∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
      GLAPComponent 3 (fixSubgroup α) (J.subgroupOf K) := by
    intro J hJ
    have h1 := glaPComponent_subgroupOf hp
      (inf_le_left : K ⊓ Subgroup.centralizer ({a} : Set X) ≤ K) hJ
    rwa [subgroupOf_inf_centralizer_eq hk hc, ← hfixα] at h1
  rcases hshape (π k') hbar1 hbarp with hcon | ⟨L, hL, hu, hG⟩
  · refine Or.inl fun J hJ => ?_
    have h2 := glaPComponent_map_fixSubgroup π hker α β hαβ hπ hp (hJsub J hJ)
    rw [hfixβ] at h2
    exact no_glaPComponent_of_pConstrainedShape hp hcon h2
  · refine Or.inr ?_
    have hL' : GLAPComponent 3 (fixSubgroup β) L := by rw [hfixβ]; exact hL
    obtain ⟨J₀', hJ₀', hJ₀map⟩ := exists_glaPComponent_map_fixSubgroup π hker α β hαβ hπ hp hL'
    refine ⟨J₀'.map K.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
    · intro J hJ
      have hJK : J ≤ K := hJ.1.trans inf_le_left
      have h2 := glaPComponent_map_fixSubgroup π hker α β hαβ hπ hp (hJsub J hJ)
      rw [hfixβ] at h2
      have hmapJ : (J.subgroupOf K).map π = L := hu _ h2
      have heq : J.subgroupOf K = J₀' :=
        eq_of_map_eq_of_perfect π hker
          (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect (hJsub J hJ))
          (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ₀')
          (hmapJ.trans hJ₀map.symm)
      rw [← Subgroup.map_subgroupOf_eq_of_le hJK, heq]
    · have h1 : (J₀'.map K.subtype).subgroupOf K = J₀' :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective J₀'
      rw [h1]
      have hcL : GLAPPrimeCore 3 ↥L = ⊥ :=
        glaPPrimeCore_eq_bot_of_subnormal hp hL'.2.1 hO
      have hOα : GLAPPrimeCoreOf 3 (fixSubgroup α) = ⊥ :=
        glaPPrimeCoreOf_fixSubgroup_eq_bot π hker α β hαβ hπ hp hZp hO
      have hcJ : GLAPPrimeCore 3 ↥J₀' = ⊥ :=
        glaPPrimeCore_eq_bot_of_subnormal hp hJ₀'.2.1 hOα
      have hcL' : GLAPPrimeCore 3 ↥(J₀'.map π) = ⊥ := by rw [hJ₀map]; exact hcL
      have hperf : ⁅J₀', J₀'⁆ = J₀' := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ₀'
      have e := pSimpleEquivOfCentralMap π hker hperf hcJ hcL'
      rw [hJ₀map] at e
      rcases hG with hleaf | ⟨hA6, hsplit⟩
      · have hleaf' : LeafType 3 (PSimple 3 J₀') := LeafType.of_equiv e.symm hleaf
        exact ⟨Or.inl hleaf', fun hne => (hleaf'.not_nonempty_alt6 hne).elim⟩
      · obtain ⟨-, ⟨g⟩⟩ := hA6
        have hZ : Subgroup.center ↥J₀' = ⊥ :=
          center_lift_eq_bot π hker hπ hZp hperf (hJ₀map ▸ hsplit)
        refine ⟨Or.inr (Or.inl ⟨rfl, ⟨e.symm.symm.trans g⟩⟩), ?_⟩
        exact RkTriv3.of_equiv ((QuotientGroup.quotientMulEquivOfEq hcJ).trans
          QuotientGroup.quotientBot).symm (fun _ => hZ)

end CoverDichSplit

section CoverStepSplit

variable {X : Type} [Group X] [Finite X]

theorem strong_of_centShapeSplit_cover {K B : Subgroup X}
    {name : TauCeti.SporadicName} (hOut : SporadicOuterLeTwo) (hH : CompHyp 3 K B)
    (hN : I271Norm 3 K B) (hS : I271SporType K name)
    (hloc : IsLocallyOneBalancedAbs 3 (↥K ⧸ Subgroup.center ↥K))
    (hOall : OPrimeCoreTrivialAt 3 (↥K ⧸ Subgroup.center ↥K)) (hChev : ChevStrong 3)
    (hshape : CentShapeSplit 3 (↥K ⧸ Subgroup.center ↥K)) : IsStronglyBalancedIn 3 B K := by
  have hZp : IsPGroup 3 (Subgroup.center ↥K) := i271h_center_isPGroup hH.prime hH.primeCore
  refine strong_of_dichotomy_rk (Good := GoodSpor 3 []) (Rk := RkTriv3)
    (fun _ _ _ _ e h => GoodSpor.of_equiv e h) (fun _ _ _ _ e h => RkTriv3.of_equiv e h)
    hOut hH hN hS hloc (fun _ _ _ _ _ h hG hR => strong_goodA6 hChev h hG hR) ?_
  intro a k hk haB hc haC
  obtain ⟨hkZ, hkp⟩ := lift_data_of_inner (hH.elem.2 a haB) haC hk hc
  exact comp_dichotomy_coverSplit hZp hOall hshape hk hc hkZ hkp

theorem sporStrong_of_centShapeSplit_cover
    {name : TauCeti.SporadicName} (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds name 3) (hChev : ChevStrong 3)
    (hD : CentShapeSplit 3 (NativeSporadic.Carrier name)) : SporStrong name 3 := by
  intro Y _ _ K B hC hN hS
  have hq : CFSG.Open.IsQuasisimple ↥K := hC.quasi
  obtain ⟨e⟩ := hS
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hloc : IsLocallyOneBalancedAbs 3 (↥K ⧸ Subgroup.center ↥K) :=
    isLocallyOneBalancedAbs_of_pair hOut hBr hC.prime hC.odd hP _ hq.2
      (exists_noncomm_of_isQuasisimple hq) ⟨e⟩
  let eS : (↥K ⧸ Subgroup.center ↥K) ≃* NativeSporadic.Carrier name :=
    e.trans (hBr name).some.symm
  haveI : Finite (NativeSporadic.Carrier name) := Finite.of_equiv _ eS.toEquiv
  have hOall : OPrimeCoreTrivialAt 3 (↥K ⧸ Subgroup.center ↥K) := hP.1 _ ⟨eS⟩
  have hshape : CentShapeSplit 3 (↥K ⧸ Subgroup.center ↥K) :=
    CentShapeSplit.of_equiv Nat.prime_three eS.symm hD
  exact strong_of_centShapeSplit_cover hOut hC hN ⟨e⟩ hloc hOall hChev hshape

end CoverStepSplit

end CFSG.HardMathSupport.Dickson.I271
