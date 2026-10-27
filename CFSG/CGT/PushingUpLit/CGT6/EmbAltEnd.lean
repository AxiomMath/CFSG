module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltEndSetup
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltPS
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltY
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltRec
public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.Main

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv
open CFSG.EvenSmallLie.OddTranspAlt (cls)
open scoped commutatorElement

@[expose] def Alt419 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), EndCfg4 G T Y → ∀ m : ℕ, 7 ≤ m → Odd m → YAlt Y m →
      ∀ t : ↥G, orderOf t = 2 → (t : MulAut V) ∈ T →
        ∀ x ∈ cls t, ∀ y ∈ cls t, Odd (orderOf (x * y)) ∨ orderOf (x * y) = 2

@[expose] def Alt2Rank1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), EndCfg4 G T Y → ∀ m : ℕ, 7 ≤ m → Odd m → YAlt Y m →
      ∀ a b : MulAut V, a ∈ G → b ∈ G → a ∈ Subgroup.centralizer (Y : Set (MulAut V)) →
        b ∈ Subgroup.centralizer (Y : Set (MulAut V)) → a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 →
        a ≠ b → a * b = b * a → False



private theorem normal_closure_cls {Γ : Type*} [Group Γ] (t : Γ) :
    (Subgroup.closure (cls t)).Normal := by
  constructor
  intro x hx g
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (CFSG.EvenSmallLie.OddTranspAlt.conj_mem_cls hx g)
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact mul_mem ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem ha

private theorem commutator_subgroupOf_self {Γ : Type*} [Group Γ] {N Y : Subgroup Γ} (hYN : Y ≤ N)
    (hperf : ⁅Y, Y⁆ = Y) : ⁅Y.subgroupOf N, Y.subgroupOf N⁆ = Y.subgroupOf N := by
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hYN, hperf]


section L0

variable {V : Type} [CommGroup V]

theorem exists_L0 {G Y : Subgroup (MulAut V)} (hYG : Y ≤ G) {n : ℕ} (hn : 5 ≤ n)
    (hYA : Nonempty (↥Y ≃* alternatingGroup (Fin n))) (hperf : ⁅Y, Y⁆ = Y) {t : ↥G}
    (htY : (t : MulAut V) ∈ Subgroup.centralizer (Y : Set (MulAut V)))
    (φ : Subgroup.closure (cls t) ≃* Perm (Fin (n + 2)))
    (hφ : ∀ x : Subgroup.closure (cls t), (x : ↥G) ∈ cls t ↔ (φ x).IsSwap)
    (hYN : Y.subgroupOf G ≤ Subgroup.closure (cls t)) :
    ∃ (L : Subgroup (MulAut V)) (θ : ↥L ≃* alternatingGroup (Fin (n + 2))) (a b : Fin (n + 2)),
      a ≠ b ∧ Y ≤ L ∧ L ≤ G ∧ (L.subgroupOf G).Normal ∧
      (Y.subgroupOf L).map θ.toMonoidHom = altStabilizer (n + 2) {a, b} := by
  classical
  obtain ⟨ε⟩ := hYA
  let N : Subgroup ↥G := Subgroup.closure (cls t)
  have hNn : N.Normal := normal_closure_cls t
  have h5 : 5 ≤ Nat.card (Fin (n + 2)) := by simp; omega
  have hAlt : commutator (Perm (Fin (n + 2))) = alternatingGroup (Fin (n + 2)) :=
    alternatingGroup.commutator_perm_eq h5
  let L₂ : Subgroup ↥G := ⁅N, N⁆
  have hL₂ : L₂.Normal := Subgroup.commutator_normal N N
  let L : Subgroup (MulAut V) := L₂.map G.subtype
  have hLG : L ≤ G := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hLsub : L.subgroupOf G = L₂ :=
    Subgroup.comap_map_eq_self_of_injective G.subtype_injective L₂
  have hmapc : (commutator ↥N).map φ.toMonoidHom = alternatingGroup (Fin (n + 2)) := by
    rw [commutator, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective, ← hAlt]
    rfl
  have hL₂N : L₂ ≤ N := Subgroup.commutator_le_left N N
  have hLN : ∀ l : ↥L, (⟨(l : MulAut V), hLG l.2⟩ : ↥G) ∈ N := by
    intro l
    apply hL₂N
    rw [← hLsub]
    exact l.2
  have hLc : ∀ l : ↥L, ∃ z ∈ commutator ↥N, (z : ↥G) = ⟨(l : MulAut V), hLG l.2⟩ := by
    intro l
    have h1 : (⟨(l : MulAut V), hLG l.2⟩ : ↥G) ∈ L₂ := by
      rw [← hLsub]
      exact l.2
    have h2 : L₂ = (commutator ↥N).map N.subtype := (Subgroup.map_subtype_commutator N).symm
    rw [h2] at h1
    obtain ⟨z, hz, hzl⟩ := h1
    exact ⟨z, hz, hzl⟩
  let ρ : ↥L →* alternatingGroup (Fin (n + 2)) :=
    { toFun := fun l => ⟨φ ⟨⟨(l : MulAut V), hLG l.2⟩, hLN l⟩, by
        obtain ⟨z, hz, hzl⟩ := hLc l
        have h3 : (⟨⟨(l : MulAut V), hLG l.2⟩, hLN l⟩ : ↥N) = z := Subtype.ext hzl.symm
        rw [h3, ← hmapc]
        exact ⟨z, hz, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        show φ ⟨⟨(1 : ↥L), _⟩, _⟩ = 1
        exact (map_one φ : φ 1 = 1)
      map_mul' := by
        intro l₁ l₂
        apply Subtype.ext
        show φ ⟨⟨((l₁ * l₂ : ↥L) : MulAut V), _⟩, _⟩ =
          φ ⟨⟨(l₁ : MulAut V), _⟩, _⟩ * φ ⟨⟨(l₂ : MulAut V), _⟩, _⟩
        rw [← map_mul]
        rfl }
  have hρ : ∀ (l : ↥L) (x : ↥N), (x : ↥G) = ⟨(l : MulAut V), hLG l.2⟩ →
      ((ρ l : alternatingGroup (Fin (n + 2))) : Perm (Fin (n + 2))) = φ x := by
    intro l x hx
    have : x = ⟨⟨(l : MulAut V), hLG l.2⟩, hLN l⟩ := Subtype.ext hx
    rw [this]
    rfl
  have hρinj : Function.Injective ρ := by
    intro l₁ l₂ h
    have h1 := congrArg Subtype.val h
    rw [hρ l₁ ⟨⟨(l₁ : MulAut V), hLG l₁.2⟩, hLN l₁⟩ rfl,
      hρ l₂ ⟨⟨(l₂ : MulAut V), hLG l₂.2⟩, hLN l₂⟩ rfl] at h1
    have h2 := φ.injective h1
    exact Subtype.ext (congrArg (fun x : ↥N => ((x : ↥G) : MulAut V)) h2)
  have hρsurj : Function.Surjective ρ := by
    intro τ
    have hτ : (τ : Perm (Fin (n + 2))) ∈ (commutator ↥N).map φ.toMonoidHom := by
      rw [hmapc]
      exact τ.2
    obtain ⟨z, hz, hzτ⟩ := hτ
    have hzL : ((z : ↥G) : MulAut V) ∈ L := by
      refine ⟨(z : ↥G), ?_, rfl⟩
      have h2 : L₂ = (commutator ↥N).map N.subtype := (Subgroup.map_subtype_commutator N).symm
      rw [h2]
      exact ⟨z, hz, rfl⟩
    refine ⟨⟨((z : ↥G) : MulAut V), hzL⟩, Subtype.ext ?_⟩
    rw [hρ ⟨((z : ↥G) : MulAut V), hzL⟩ z rfl]
    exact hzτ
  let θ : ↥L ≃* alternatingGroup (Fin (n + 2)) := MulEquiv.ofBijective ρ ⟨hρinj, hρsurj⟩
  have hθ : ∀ (l : ↥L) (x : ↥N), (x : ↥G) = ⟨(l : MulAut V), hLG l.2⟩ →
      ((θ l : alternatingGroup (Fin (n + 2))) : Perm (Fin (n + 2))) = φ x := hρ
  have hY'perf : ⁅Y.subgroupOf G, Y.subgroupOf G⁆ = Y.subgroupOf G :=
    commutator_subgroupOf_self hYG hperf
  have hY'L₂ : Y.subgroupOf G ≤ L₂ :=
    calc Y.subgroupOf G = ⁅Y.subgroupOf G, Y.subgroupOf G⁆ := hY'perf.symm
      _ ≤ ⁅N, N⁆ := Subgroup.commutator_mono hYN hYN
  have hYL : Y ≤ L := fun y hy => ⟨⟨y, hYG hy⟩, hY'L₂ hy, rfl⟩
  have htN : t ∈ N := Subgroup.subset_closure CFSG.EvenSmallLie.OddTranspAlt.self_mem_cls
  obtain ⟨a, b, hab, hswap⟩ :=
    (hφ ⟨t, htN⟩).1 CFSG.EvenSmallLie.OddTranspAlt.self_mem_cls
  refine ⟨L, θ, a, b, hab, hYL, hLG, by rw [hLsub]; exact hL₂, ?_⟩
  let H : Subgroup (Perm (Fin (n + 2))) := ((Y.subgroupOf G).subgroupOf N).map φ.toMonoidHom
  have hHperf : ⁅H, H⁆ = H := by
    rw [← Subgroup.map_commutator, commutator_subgroupOf_self hYN hY'perf]
  have hHcomm : ∀ σ ∈ H, σ * swap a b = swap a b * σ := by
    rintro _ ⟨x, hx, rfl⟩
    have hxY : ((x : ↥G) : MulAut V) ∈ Y := hx
    have h1 := Subgroup.mem_centralizer_iff.mp htY _ hxY
    have h2 : x * ⟨t, htN⟩ = ⟨t, htN⟩ * x := Subtype.ext (Subtype.ext h1)
    show φ x * swap a b = swap a b * φ x
    rw [← hswap, ← map_mul, ← map_mul, h2]
  have hHcard : Nat.card ↥H = n.factorial / 2 := by
    have hn2 : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYG).toEquiv, Nat.card_congr ε.toEquiv,
      nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hHeq := eq_altStabilizer_of_perfect_comm_swap (by omega) hab hHperf hHcomm hHcard
  ext τ
  constructor
  · rintro ⟨l, hl, rfl⟩
    have hlY : (l : MulAut V) ∈ Y := hl
    let x : ↥N := ⟨⟨(l : MulAut V), hLG l.2⟩, hLN l⟩
    have hxH : φ x ∈ H := ⟨x, hlY, rfl⟩
    rw [hHeq] at hxH
    obtain ⟨τ', hτ', hτ'x⟩ := hxH
    have h1 : θ.toMonoidHom l = τ' := Subtype.ext ((hθ l x rfl).trans hτ'x.symm)
    rw [h1]
    exact hτ'
  · intro hτ
    have hτH : (τ : Perm (Fin (n + 2))) ∈ H := by
      rw [hHeq]
      exact ⟨τ, hτ, rfl⟩
    obtain ⟨x, hxY, hxτ⟩ := hτH
    let l : ↥L := θ.symm τ
    let x' : ↥N := ⟨⟨(l : MulAut V), hLG l.2⟩, hLN l⟩
    have h1 : φ x' = φ x := by
      have hl : θ l = τ := θ.apply_symm_apply τ
      rw [← hθ l x' rfl, hl]
      exact hxτ.symm
    have h2 : x' = x := φ.injective h1
    have hlY : (l : MulAut V) ∈ Y := by
      have : ((x : ↥G) : MulAut V) = (l : MulAut V) :=
        congrArg (fun z : ↥N => ((z : ↥G) : MulAut V)) h2.symm
      rw [← this]
      exact hxY
    exact ⟨l, hlY, θ.apply_symm_apply τ⟩

end L0



section Irr

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem EndCfg4.fixV_commV_of_normal (h : EndCfg4 G T Y) {L : Subgroup (MulAut V)} (hLG : L ≤ G)
    (hN : (L.subgroupOf G).Normal) (hL1 : Nontrivial ↥L) :
    (∀ w : V, (∀ x : L, (x : MulAut V) w = w) → w = 1) ∧ commV L = ⊤ := by
  have hconj : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    exact hN.conj_mem ⟨l, hLG hl⟩ hl ⟨g, hg⟩
  obtain ⟨l₀, hl₀⟩ : ∃ l : ↥L, l ≠ 1 := exists_ne 1
  have hl₀' : (l₀ : MulAut V) ≠ 1 := fun h1 => hl₀ (Subtype.ext h1)
  have hfaithful : ∀ P : Subgroup V, (∀ l ∈ L, ∀ v ∈ P, l v = v) →
      (∀ v : V, v ∈ P) → False := by
    intro P hP hall
    apply hl₀'
    ext v
    exact hP l₀ l₀.2 v (hall v)
  constructor
  · have hinv : GInv G (fixV L) := by
      intro g hg w hw
      rw [mem_fixV] at hw ⊢
      intro l hl
      have h1 := hw (g⁻¹ * l * g) (by simpa using hconj g⁻¹ (inv_mem hg) l hl)
      calc l (g w) = g ((g⁻¹ * l * g) w) := by simp [MulAut.mul_apply]
        _ = g w := by rw [h1]
    rcases h.irr (fixV L) hinv with h0 | h1
    · intro w hw
      have : w ∈ fixV L := mem_fixV.mpr fun x hx => hw ⟨x, hx⟩
      rw [h0] at this
      exact Subgroup.mem_bot.mp this
    · exact (hfaithful (fixV L) (fun l hl v hv => mem_fixV.mp hv l hl)
        (fun v => by rw [h1]; trivial)).elim
  · have hinv : GInv G (commV L) := by
      intro g hg w hw
      induction hw using Subgroup.closure_induction with
      | mem w hw =>
        obtain ⟨l, hl, v, rfl⟩ := hw
        have h1 : g (l v * v⁻¹) = (g * l * g⁻¹) (g v) * (g v)⁻¹ := by
          simp [MulAut.mul_apply]
        rw [h1]
        exact Subgroup.subset_closure ⟨g * l * g⁻¹, hconj g hg l hl, g v, rfl⟩
      | one => simp
      | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
      | inv a _ ha => rw [map_inv]; exact inv_mem ha
    rcases h.irr (commV L) hinv with h0 | h1
    · exfalso
      apply hl₀'
      ext v
      have : (l₀ : MulAut V) v * v⁻¹ ∈ commV L :=
        Subgroup.subset_closure ⟨(l₀ : MulAut V), l₀.2, v, rfl⟩
      rw [h0, Subgroup.mem_bot, mul_inv_eq_one] at this
      exact this
    · exact h1

end Irr


section Assembly

variable {V : Type} [CommGroup V] [Finite V]

theorem EndCfg4.exists_natSection {G T Y : Subgroup (MulAut V)} (h : EndCfg4 G T Y)
    (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ}
    (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m) :
    ∃ θ₀ : ↥Y ≃* alternatingGroup (Fin m), IsNatSectionWith (altAct m) θ₀ (commV Y) ⊥ := by
  obtain ⟨ε⟩ := hY
  have hX : InClassX ↥(yuHol Y) := by
    rcases h.hcls2 with hX | ⟨n, hn, hΩ⟩
    · exact hX
    · exfalso
      obtain ⟨-, θΩ, -⟩ := hΩ
      have h1 := YSL.card_eq (by omega) (⟨θΩ⟩ : YSL Y (2 * n))
      rw [Nat.card_congr ε.toEquiv] at h1
      exact card_alt_ne_card_sl2 hm (by omega : 2 ≤ 2 * n) h1
  exact natSection_of_classX_alt hV h.adm.hperf hX hm hodd ⟨ε⟩

theorem end4Alt_of (hNL : NatLiftStatement) (h2 : Alt2Rank1) (hOT : Alt419) : End4Alt := by
  intro V _ _ hV G T Y h m hm hodd hY
  have hperf : ⁅Y, Y⁆ = Y := h.adm.hperf
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  obtain ⟨t, ht, htT, htY⟩ := h.exists_involution
  have hot := hOT V hV G T Y h m hm hodd hY t ht htT
  have hcomp := h.isComponentOf hm hY ht htY
  have hYN := h.le_closure_cls ht
  obtain ⟨ε⟩ := hY
  have hYA : Nonempty (↥(Y.subgroupOf G) ≃* alternatingGroup (Fin m)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hYG).trans ε⟩
  have hk2 : ∀ e ∈ cls t, e ≠ t → t * e = e * t →
      e ∉ Subgroup.centralizer ((Y.subgroupOf G : Subgroup ↥G) : Set ↥G) := by
    intro e he hne hcomm hcent
    have he2 : orderOf e = 2 := CFSG.EvenSmallLie.OddTranspAlt.orderOf_of_mem_cls_of ht he
    have hcY : (e : MulAut V) ∈ Subgroup.centralizer (Y : Set (MulAut V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := Subgroup.mem_centralizer_iff.mp hcent ⟨y, hYG hy⟩ hy
      exact congrArg Subtype.val this
    refine h2 V hV G T Y h m hm hodd ⟨ε⟩ (t : MulAut V) (e : MulAut V) t.2 e.2 htY hcY
      ?_ ?_ ?_ ?_ ?_ ?_
    · have h1 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
      rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
    · have h1 : e ^ 2 = 1 := by rw [← he2]; exact pow_orderOf_eq_one e
      rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
    · intro h1
      have : t = 1 := Subtype.ext h1
      rw [this] at ht
      simp at ht
    · intro h1
      have : e = 1 := Subtype.ext h1
      rw [this] at he2
      simp at he2
    · intro h1
      exact hne (Subtype.ext h1.symm)
    · exact congrArg Subtype.val hcomm
  obtain ⟨φ, hφ⟩ := CFSG.EvenSmallLie.OddTranspAlt.oddTranspAlt ht hot hm hcomp hYN hYA hk2
  obtain ⟨L, θ, a, b, hab, hYL, hLG, hLn, hstab⟩ :=
    exists_L0 hYG (by omega) ⟨ε⟩ hperf htY φ hφ hYN
  obtain ⟨θ₀, hnat⟩ := h.exists_natSection hV hm hodd ⟨ε⟩
  have hLnt : Nontrivial ↥L := by
    have : Nontrivial (alternatingGroup (Fin (m + 2))) :=
      alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
    exact θ.toEquiv.nontrivial
  obtain ⟨hC, hVL⟩ := h.fixV_commV_of_normal hLG hLn hLnt
  have hrec := rec418 hV hodd hm θ hab hYL hstab θ₀ hnat hC hVL
  obtain ⟨c, rfl⟩ := hodd
  have hlift := hNL V hV L Y (c + 1) c (by omega) (by omega) (by omega) θ hrec {a, b}
    (by rw [Finset.card_pair hab]; omega) hYL hstab
  exact h.nolift ⟨L, hYL, hLG, hLn.isSubnormal, Or.inl hlift⟩

end Assembly

end CFSG.CGT.PushingUpLit.CGT6
