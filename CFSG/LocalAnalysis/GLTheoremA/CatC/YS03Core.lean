module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma31Proof
public import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Component
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def StrongBalAt (p : ℕ) (S : Type) [Group S] : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K B : Subgroup X), GLAPPrimeCore p X = ⊥ →
    GLAPComponent p ⊤ K → Nonempty (↥K ≃* S) → IsSCp p ⊤ B →
    B ≤ Subgroup.normalizer (K : Set X) → IsStronglyBalancedIn p B K

section Basic

variable {S : Type} [Group S]

theorem ys03_conj_injective (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  have : a ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun f : MulAut S => f y) (MonoidHom.mem_ker.1 ha)
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  rwa [hZ, Subgroup.mem_bot] at this

theorem ys03_eq_one_of_commute (hZ : Subgroup.center S = ⊥) {w : MulAut S}
    (hw : ∀ s : S, w * MulAut.conj s = MulAut.conj s * w) : w = 1 := by
  ext y
  have h1 : ∀ s : S, w s = s := by
    intro s
    apply ys03_conj_injective hZ
    have := hw s
    calc MulAut.conj (w s) = w * MulAut.conj s * w⁻¹ := by
          ext z; simp [MulAut.conj_apply]
      _ = MulAut.conj s := by rw [this]; group
  simpa using h1 y

end Basic

section Core

instance ys03_finite_mulAut (S : Type) [Group S] [Finite S] : Finite (MulAut S) :=
  Finite.of_injective (fun f : MulAut S => (f : S → S)) (fun f g h => MulEquiv.ext (congrFun h))

theorem ys03_exists_isSCp_above {G : Type} [Group G] [Finite G] {p : ℕ} {W : Subgroup G}
    (hW : IsElemAbelian p W) : ∃ A₁ : Subgroup G, IsSCp p ⊤ A₁ ∧ W ≤ A₁ := by
  obtain ⟨A₁, hWA₁, hmax⟩ :=
    (Set.toFinite {E : Subgroup G | W ≤ E ∧ IsElemAbelian p E}).exists_le_maximal ⟨le_rfl, hW⟩
  exact ⟨A₁, ⟨le_top, hmax.1.2, fun E' _ hE'el hle =>
    le_antisymm (hmax.2 ⟨hWA₁.trans hle, hE'el⟩ hle) hle⟩, hWA₁⟩

theorem ys03_isElemAbelian_zpowers {G : Type} [Group G] {p : ℕ} {z : G} (hz : z ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers z) := by
  refine ⟨inferInstance, ?_⟩
  intro g hg
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]

theorem ys03_coreFree_of_strongBal {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) {p : ℕ} (hp : p.Prime) (hpS : p ∣ Nat.card S)
    (hSB : StrongBalAt p S) {x : MulAut S} (hx : x ^ p = 1) {H : Subgroup (MulAut S)}
    (hH : innerAut S ≤ H) (hxH : x ∈ Subgroup.normalizer (H : Set (MulAut S))) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hS
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm)
  have hinj := ys03_conj_injective hZ
  set Y : Subgroup (MulAut S) := H ⊔ Subgroup.zpowers x with hY
  have hHY : H ≤ Y := le_sup_left
  have hxY : x ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hIY : innerAut S ≤ Y := hH.trans hHY
  have hYN : Y ≤ Subgroup.normalizer (H : Set (MulAut S)) :=
    sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).2 hxH)
  haveI hIn : (innerAut S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨c, rfl⟩ := hn
    refine ⟨g c, ?_⟩
    ext y
    simp [MulAut.conj_apply]
  set K : Subgroup ↥Y := (innerAut S).subgroupOf Y with hK
  haveI hKn : K.Normal := Subgroup.Normal.subgroupOf hIn Y
  let eK : ↥K ≃* S :=
    (Subgroup.subgroupOfEquivOfLe hIY).trans (MonoidHom.ofInjective hinj).symm
  haveI : IsSimpleGroup ↥K := eK.isSimpleGroup
  have hncK : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨eK.symm a, eK.symm b, fun h => hab (eK.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hpK : p ∣ Nat.card ↥K := by rw [Nat.card_congr eK.toEquiv]; exact hpS
  have hconjK : ∀ s : S, (⟨MulAut.conj s, hIY ⟨s, rfl⟩⟩ : ↥Y) ∈ K := fun s =>
    Subgroup.mem_subgroupOf.2 ⟨s, rfl⟩
  have hcoreY : GLAPPrimeCore p ↥Y = ⊥ := by
    set N : Subgroup ↥Y := GLAPPrimeCore p ↥Y with hN
    haveI hNn : N.Normal := GLAPPrimeCore.normal p _
    have hNK0 : N.subgroupOf K = ⊥ := by
      haveI : (N.subgroupOf K).Normal := Subgroup.Normal.subgroupOf hNn K
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf K) with h | h
      · exact h
      · exfalso
        have hKN : K ≤ N := by
          intro k hk
          have : (⟨k, hk⟩ : ↥K) ∈ N.subgroupOf K := by rw [h]; trivial
          exact this
        have hdvd : p ∣ Nat.card N := hpK.trans (Subgroup.card_dvd_of_le hKN)
        exact (Nat.Prime.coprime_iff_not_dvd hp).1
          (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥Y)) hdvd
    have hcomm : ∀ n ∈ N, ∀ k ∈ K, n * k = k * n := by
      intro n hn k hk
      have h1 : n * k * n⁻¹ * k⁻¹ ∈ N := by
        have := N.mul_mem hn (hNn.conj_mem n⁻¹ (N.inv_mem hn) k)
        simpa [mul_assoc] using this
      have h2 : n * k * n⁻¹ * k⁻¹ ∈ K := K.mul_mem (hKn.conj_mem k hk n) (K.inv_mem hk)
      have h3 : (⟨n * k * n⁻¹ * k⁻¹, h2⟩ : ↥K) ∈ N.subgroupOf K := h1
      rw [hNK0, Subgroup.mem_bot] at h3
      have h4 : n * k * n⁻¹ * k⁻¹ = 1 := congrArg Subtype.val h3
      calc n * k = n * k * n⁻¹ * k⁻¹ * (k * n) := by group
        _ = k * n := by rw [h4, one_mul]
    refine eq_bot_iff.2 fun n hn => ?_
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply ys03_eq_one_of_commute hZ
    intro s
    exact congrArg Subtype.val (hcomm n hn _ (hconjK s))
  have hcomp : GLAPComponent p (⊤ : Subgroup ↥Y) K :=
    GL83.PiGen.glaPComponent_of_normal_simple hp le_top (hKn.subgroupOf _) hncK hpK
  set xY : ↥Y := ⟨x, hxY⟩ with hxYdef
  have hxYp : xY ^ p = 1 := Subtype.ext (by simpa [hxYdef] using hx)
  obtain ⟨B, hBsc, hW0B⟩ := ys03_exists_isSCp_above (ys03_isElemAbelian_zpowers hxYp)
  have hxB : xY ∈ B := hW0B (Subgroup.mem_zpowers xY)
  have hBN : B ≤ Subgroup.normalizer (K : Set ↥Y) :=
    le_trans le_top (Subgroup.normalizer_eq_top_iff.2 hKn).ge
  have hbal := hSB ↥Y K B hcoreY hcomp ⟨eK⟩ hBsc hBN
  set Cx : Subgroup (MulAut S) := H ⊓ Subgroup.centralizer ({x} : Set (MulAut S)) with hCx
  set Wsub : Subgroup (MulAut S) := GLAPPrimeCoreOf p Cx with hWsub
  have hWleC : Wsub ≤ Cx := by
    intro w hw
    rw [hWsub] at hw
    unfold GLAPPrimeCoreOf at hw
    obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hw
    exact k.2
  have hWle : Wsub ≤ Y := hWleC.trans (inf_le_left.trans hHY)
  set Wt : Subgroup ↥Y := Wsub.subgroupOf Y with hWt
  have hWt_cop : Nat.Coprime p (Nat.card Wt) := by
    have : Nat.card Wt = Nat.card Wsub :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWle).toEquiv
    rw [this]
    exact CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp Cx
  have hBW : B ⊓ Subgroup.normalizer (K : Set ↥Y) ≤ Subgroup.normalizer (Wt : Set ↥Y) := by
    intro b hb
    have hbB : b ∈ B := hb.1
    have hbx' : b * xY = xY * b := by
      have := hBsc.2.1.1.1.comm (⟨b, hbB⟩ : ↥B) ⟨xY, hxB⟩
      simpa using congrArg Subtype.val this
    have hbx : (b : MulAut S) * x = x * (b : MulAut S) := congrArg Subtype.val hbx'
    have hbH : (b : MulAut S) ∈ Subgroup.normalizer (H : Set (MulAut S)) := hYN b.2
    have hbxb : (b : MulAut S) * x * (b : MulAut S)⁻¹ = x := by rw [hbx]; group
    have hbC : (b : MulAut S) ∈ Subgroup.normalizer (Cx : Set (MulAut S)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [hCx, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_singleton_iff]
      refine and_congr (Subgroup.mem_normalizer_iff.1 hbH y) ?_
      constructor
      · intro hy
        calc (b : MulAut S) * y * (b : MulAut S)⁻¹ * x
            = (b * y * (b : MulAut S)⁻¹) * ((b : MulAut S) * x * (b : MulAut S)⁻¹) := by rw [hbxb]
          _ = (b : MulAut S) * (y * x) * (b : MulAut S)⁻¹ := by group
          _ = (b : MulAut S) * (x * y) * (b : MulAut S)⁻¹ := by rw [hy]
          _ = ((b : MulAut S) * x * (b : MulAut S)⁻¹) * ((b : MulAut S) * y * (b : MulAut S)⁻¹) := by
              group
          _ = x * ((b : MulAut S) * y * (b : MulAut S)⁻¹) := by rw [hbxb]
      · intro hy
        have h2 : (b : MulAut S) * (y * x) * (b : MulAut S)⁻¹ =
            (b : MulAut S) * (x * y) * (b : MulAut S)⁻¹ := by
          calc (b : MulAut S) * (y * x) * (b : MulAut S)⁻¹
              = ((b : MulAut S) * y * (b : MulAut S)⁻¹) * ((b : MulAut S) * x * (b : MulAut S)⁻¹) := by
                group
            _ = ((b : MulAut S) * y * (b : MulAut S)⁻¹) * x := by rw [hbxb]
            _ = x * ((b : MulAut S) * y * (b : MulAut S)⁻¹) := hy
            _ = ((b : MulAut S) * x * (b : MulAut S)⁻¹) * ((b : MulAut S) * y * (b : MulAut S)⁻¹) := by
                rw [hbxb]
            _ = (b : MulAut S) * (x * y) * (b : MulAut S)⁻¹ := by group
        exact mul_left_cancel (mul_right_cancel h2)
    have hCb : GLBConj (b : MulAut S) Cx = Cx := mem_normalizer_iff_gLBConj_eq.1 hbC
    have hW1 : GLBConj (b : MulAut S) Wsub = Wsub := by
      have h := glaPPrimeCoreOf_gLBConj p (b : MulAut S) Cx
      rw [hCb] at h
      exact h.symm
    have hbW : (b : MulAut S) ∈ Subgroup.normalizer (Wsub : Set (MulAut S)) :=
      mem_normalizer_iff_gLBConj_eq.2 hW1
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [hWt, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hbW (w : MulAut S)
  have hconc : Wt ≤ Subgroup.centralizer (K : Set ↥Y) :=
    hbal Wt (le_trans le_top (Subgroup.normalizer_eq_top_iff.2 hKn).ge) hWt_cop hBW
  refine eq_bot_iff.2 fun w hw => ?_
  rw [Subgroup.mem_bot]
  apply ys03_eq_one_of_commute hZ
  intro s
  have hwY : w ∈ Y := hWle hw
  have h1 := Subgroup.mem_centralizer_iff.1 (hconc (show (⟨w, hwY⟩ : ↥Y) ∈ Wt from hw)) _
    (hconjK s)
  exact (congrArg Subtype.val h1).symm

end Core


@[expose] def CoreFreeAt (p : ℕ) (S : Type) [Group S] : Prop :=
  ∀ x : MulAut S, x ^ p = 1 → x ≠ 1 → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
    x ∈ Subgroup.normalizer (H : Set (MulAut S)) →
      GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥

theorem ys03_localDelta_le {p : ℕ} {M : Type*} [Group M] (H D : Subgroup M) {x : M} (hxD : x ∈ D)
    (hx1 : x ≠ 1) :
    localDeltaIn p H D ≤ GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set M)) := by
  unfold localDeltaIn
  exact iInf₂_le_of_le x hxD (iInf_le_of_le hx1 le_rfl)

theorem ys03_weak_of_coreFree {p : ℕ} (hp : p.Prime) {S : Type} [Group S] (h : CoreFreeAt p S)
    {A : Subgroup (MulAut S)} (hA : IsElemAbelian p A) :
    IsTwoPrimaryWeaklyLocallyBalanced p 1 A := by
  intro D hD H hH hAH
  haveI : Fact p.Prime := ⟨hp⟩
  have hDne : D ≠ ⊥ := fun hb => hp.ne_one (by
    have := hD.2.2
    rw [hb, Subgroup.card_bot, pow_one] at this
    exact this.symm)
  obtain ⟨⟨x, hxD⟩, hx1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have hx1 : x ≠ 1 := fun hh => hx1' (Subtype.ext hh)
  have hxA : x ∈ A := hD.1 hxD
  have hle := ys03_localDelta_le (p := p) H D hxD hx1
  rw [h x (hA.2 x hxA) hx1 H hH (hAH hxA), le_bot_iff] at hle
  rw [hle, Subgroup.commutator_bot_left]
  simp

theorem ys03_weak_of_card_le {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    {A : Subgroup (MulAut S)} (hcard : Nat.card A ≤ p) :
    IsTwoPrimaryWeaklyLocallyBalanced p 1 A := by
  intro D hD H hH hAH
  have hDA : D = A := by
    refine Subgroup.eq_of_le_of_card_ge hD.1 ?_
    rw [hD.2.2, pow_one]
    exact hcard
  subst hDA
  have hcomm : localDeltaIn p H D ≤ Subgroup.centralizer (D : Set (MulAut S)) := by
    intro d hd a ha
    by_cases ha1 : a = 1
    · rw [ha1, one_mul, mul_one]
    · have h1 := ys03_localDelta_le (p := p) H D ha ha1 hd
      have h2 : d ∈ Subgroup.centralizer ({a} : Set (MulAut S)) :=
        (inf_le_right :
          H ⊓ Subgroup.centralizer ({a} : Set (MulAut S)) ≤ _)
          ((by
            unfold GLAPPrimeCoreOf at h1
            obtain ⟨k, -, hk⟩ := Subgroup.mem_map.1 h1
            rw [← hk]
            exact k.2) : d ∈ H ⊓ Subgroup.centralizer ({a} : Set (MulAut S)))
      exact (Subgroup.mem_centralizer_singleton_iff.1 h2).symm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcomm]
  simp

theorem ys03_innerAut_normal (S : Type) [Group S] : (innerAut S).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨c, rfl⟩ := hn
  refine ⟨g c, ?_⟩
  ext y
  simp [MulAut.conj_apply]

theorem ys03_glaPPrimeCoreOf_le {G : Type*} [Group G] {p : ℕ} (C : Subgroup G) :
    GLAPPrimeCoreOf p C ≤ C := by
  intro w hw
  unfold GLAPPrimeCoreOf at hw
  obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hw
  exact k.2

theorem ys03_weak_of_oPrime {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    (hcen : Subgroup.center S = ⊥) (hinner : ∀ y : MulAut S, y ^ p = 1 → y ∈ innerAut S)
    (h1 : ∀ s : S, orderOf s = p → GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set S)) = ⊥)
    {A : Subgroup (MulAut S)} (hA : IsElemAbelian p A) :
    IsTwoPrimaryWeaklyLocallyBalanced p 1 A := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hIn : (innerAut S).Normal := ys03_innerAut_normal S
  have hinj := ys03_conj_injective hcen
  have hAin : ∀ a ∈ A, a ∈ innerAut S := fun a ha => hinner a (hA.2 a ha)
  intro D hD H hH hAH
  have hDne : D ≠ ⊥ := fun hb => hp.ne_one (by
    have := hD.2.2
    rw [hb, Subgroup.card_bot, pow_one] at this
    exact this.symm)
  obtain ⟨⟨x, hxD⟩, hx1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have hx1 : x ≠ 1 := fun hh => hx1' (Subtype.ext hh)
  have hxA : x ∈ A := hD.1 hxD
  have hxp : x ^ p = 1 := hA.2 x hxA
  obtain ⟨s, hs⟩ := hAin x hxA
  have hsp : orderOf s = p := by
    have hs1 : s ^ p = 1 := by
      apply hinj
      rw [map_pow, hs, hxp, map_one]
    have hsne : s ≠ 1 := by
      rintro rfl
      apply hx1
      rw [← hs, map_one]
    exact orderOf_eq_prime hs1 hsne
  set Cx : Subgroup (MulAut S) := H ⊓ Subgroup.centralizer ({x} : Set (MulAut S)) with hCx
  set W : Subgroup (MulAut S) := GLAPPrimeCoreOf p Cx with hW
  have hWCx : W ≤ Cx := ys03_glaPPrimeCoreOf_le Cx
  have hWinn : ∀ t : S, MulAut.conj t ∈ W → t = 1 := by
    set T : Subgroup S := W.comap (MulAut.conj : S →* MulAut S) with hT
    have hTC : T ≤ Subgroup.centralizer ({s} : Set S) := by
      intro t ht
      have h2 : MulAut.conj t ∈ Subgroup.centralizer ({x} : Set (MulAut S)) := (hWCx ht).2
      have h3 := Subgroup.mem_centralizer_singleton_iff.1 h2
      rw [← hs, ← map_mul, ← map_mul] at h3
      exact Subgroup.mem_centralizer_singleton_iff.2 (hinj h3)
    have hTn : ∀ g ∈ Subgroup.centralizer ({s} : Set S), ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
      intro g hg t ht
      have hgH : MulAut.conj g ∈ H := hH ⟨g, rfl⟩
      have hgC : MulAut.conj g ∈ Subgroup.centralizer ({x} : Set (MulAut S)) := by
        rw [Subgroup.mem_centralizer_singleton_iff, ← hs, ← map_mul, ← map_mul]
        exact congrArg _ (Subgroup.mem_centralizer_singleton_iff.1 hg)
      have h2 := CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem (p := p) (C := Cx) (MulAut.conj g) ⟨hgH, hgC⟩ _ ht
      show MulAut.conj (g * t * g⁻¹) ∈ W
      simpa [map_mul, map_inv] using h2
    have hTcop : Nat.Coprime p (Nat.card T) := by
      have hmap : T.map (MulAut.conj : S →* MulAut S) ≤ W := Subgroup.map_comap_le _ _
      have hdvd : Nat.card (T.map (MulAut.conj : S →* MulAut S)) ∣ Nat.card W :=
        Subgroup.card_dvd_of_le hmap
      rw [Subgroup.card_map_of_injective hinj] at hdvd
      exact (CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp Cx).coprime_dvd_right
        hdvd
    have hle : T ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set S)) :=
      CFSG.HardMathSupport.Timmesfeld.Proving.le_GLAPPrimeCoreOf_of_normal hTC hTn hTcop
    rw [h1 s hsp] at hle
    intro t ht
    exact Subgroup.mem_bot.1 (hle (show t ∈ T from ht))
  have hcomm : ∀ w ∈ W, ∀ a ∈ A, w * a = a * w := by
    intro w hw a ha
    have haH : a ∈ H := hH (hAin a ha)
    have haC : a ∈ Subgroup.centralizer ({x} : Set (MulAut S)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact isElemAbelian_commute hA ha hxA
    have h2 := CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem (p := p) (C := Cx) a ⟨haH, haC⟩ w⁻¹ (W.inv_mem hw)
    have h3 : w * a * w⁻¹ * a⁻¹ ∈ W := by
      have := W.mul_mem hw h2
      simpa [mul_assoc] using this
    have h4 : w * a * w⁻¹ * a⁻¹ ∈ innerAut S := by
      have hwa : w * a * w⁻¹ ∈ innerAut S := hIn.conj_mem a (hAin a ha) w
      exact (innerAut S).mul_mem hwa ((innerAut S).inv_mem (hAin a ha))
    obtain ⟨t, ht⟩ := h4
    have ht1 : t = 1 := hWinn t (ht ▸ h3)
    have h5 : w * a * w⁻¹ * a⁻¹ = 1 := by rw [← ht, ht1, map_one]
    calc w * a = (w * a * w⁻¹ * a⁻¹) * (a * w) := by group
      _ = a * w := by rw [h5, one_mul]
  have hle := ys03_localDelta_le (p := p) H D hxD hx1
  have hDelta : localDeltaIn p H D ≤ Subgroup.centralizer (A : Set (MulAut S)) := by
    intro d hd a ha
    exact (hcomm d (hle hd) a ha).symm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer.2 hDelta]
  simp

theorem ys03_inner_of_pow_of_outer_le_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type}
    [Group K] [Finite K]
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) ≤ 2)
    {y : MulAut K} (hy : y ^ p = 1) : y ∈ innerAut K := by
  haveI : (innerAut K).Normal := ys03_innerAut_normal K
  let q : MulAut K →* CFSG.ComponentClassification.OuterAutomorphisms.Outer K :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K)
  have hsq : (q y) ^ 2 = 1 := by
    have hc : (q y) ^ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) = 1 :=
      pow_card_eq_one'
    have hpos : 0 < Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) :=
      Nat.card_pos
    interval_cases hn : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K)
    · have : q y = 1 := by simpa using hc
      rw [this, one_pow]
    · exact hc
  have h3 : (q y) ^ p = 1 := by rw [← map_pow, hy, map_one]
  have h4 : orderOf (q y) ∣ Nat.gcd p 2 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hsq)
  have hg : Nat.gcd p 2 = 1 := by
    rw [Nat.gcd_comm]
    exact (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h4
  exact (QuotientGroup.eq_one_iff y).1 h4

end CFSG.LocalAnalysis.GLTheoremA
