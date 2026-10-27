module

public import CFSG.CGT.T75B.Lift
public import CFSG.CGT.T75B.Transport

public section

namespace CFSG.CGT.T75B

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki
open scoped commutatorElement

section Root

variable {P : Type*} [Group P]

@[expose] def rootGroup (S : Sylow 2 P) : Subgroup P :=
  (Subgroup.center (S : Subgroup P)).map (S : Subgroup P).subtype

theorem mem_rootGroup {S : Sylow 2 P} {z : P} :
    z ∈ rootGroup S ↔ z ∈ (S : Subgroup P) ∧ ∀ s ∈ (S : Subgroup P), s * z = z * s := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.2, fun s hs => congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨s, hs⟩)⟩
  · rintro ⟨hz, hc⟩
    exact ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hc g.1 g.2), rfl⟩

theorem mem_smul_sylow {g : P} {S : Sylow 2 P} {z : P} :
    z ∈ ((g • S : Sylow 2 P) : Subgroup P) ↔ g⁻¹ * z * g ∈ (S : Subgroup P) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem rootGroup_smul (g : P) (S : Sylow 2 P) :
    rootGroup (g • S) = conjSubgroup g (rootGroup S) := by
  ext z
  rw [mem_rootGroup, mem_conjSubgroup, mem_rootGroup]
  simp only [mem_smul_sylow]
  constructor
  · rintro ⟨hz, hc⟩
    refine ⟨hz, fun s hs => ?_⟩
    have h1 := hc (g * s * g⁻¹) (by simpa [mul_assoc] using hs)
    calc s * (g⁻¹ * z * g) = g⁻¹ * (g * s * g⁻¹ * z) * g := by group
      _ = g⁻¹ * (z * (g * s * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * z * g) * s := by group
  · rintro ⟨hz, hc⟩
    refine ⟨hz, fun s hs => ?_⟩
    have h1 := hc (g⁻¹ * s * g) hs
    calc s * z = g * ((g⁻¹ * s * g) * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = z * s := by group

end Root

structure Lemma21Input (P : Type*) [Group P] : Prop where
  inner : ∀ (S : Sylow 2 P) (α : MulAut P), α * α = 1 →
    α ∈ (MulAut.conj : P →* MulAut P).range → (∀ x ∈ rootGroup S, α x ∈ rootGroup S) →
      ∃ t ∈ rootGroup S, α = MulAut.conj t
  outer : ∀ (S : Sylow 2 P) (α : MulAut P), α * α = 1 →
    α ∉ (MulAut.conj : P →* MulAut P).range → (∀ x ∈ rootGroup S, α x ∈ rootGroup S) →
      (∀ x ∈ rootGroup S, α x = x) ∧
        ∃ S' : Sylow 2 P, rootGroup S' ≠ rootGroup S ∧ ∀ x ∈ rootGroup S', α x = x
  trans : ∀ (S S' S'' : Sylow 2 P), rootGroup S' ≠ rootGroup S → rootGroup S'' ≠ rootGroup S →
    ∃ g ∈ Subgroup.normalizer ((rootGroup S : Subgroup P) : Set P),
      conjSubgroup g (rootGroup S') = rootGroup S''
  klein : ∀ (S S' : Sylow 2 P), rootGroup S' ≠ rootGroup S → ∀ α β : MulAut P,
    α * α = 1 → β * β = 1 → α * β = β * α →
    (∀ x ∈ rootGroup S, α x ∈ rootGroup S) → (∀ x ∈ rootGroup S', α x ∈ rootGroup S') →
    (∀ x ∈ rootGroup S, β x ∈ rootGroup S) → (∀ x ∈ rootGroup S', β x ∈ rootGroup S') →
      α = 1 ∨ β = 1 ∨ α = β

section PiTwo

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.exists_pi_two
    (hAsc : AschbacherNoPolarInput) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) :
    ∃ (f : ℕ) (P : Type) (_ : Group P) (_ : Finite P) (π : ↥(sec4Y T T₁ T₂) →* P)
      (_ : P ≃* PSU3Model f), 2 ≤ f ∧ Function.Surjective π ∧
      (∀ y : ↥(sec4Y T T₁ T₂), π y = 1 ↔ Sec4ActsTriv T T₁ T₂ (y : G)) ∧
      ∃ S S₁ : Sylow 2 P, (T.subgroupOf (sec4Y T T₁ T₂)).map π = rootGroup S ∧
        (T₁.subgroupOf (sec4Y T T₁ T₂)).map π = rootGroup S₁ ∧ rootGroup S₁ ≠ rootGroup S := by
  obtain ⟨f, P, hP, hfin, π, e, hf, hsurj, hker, S, hS⟩ := h.exists_pi hAsc hq
  obtain ⟨y₁, hy₁Y, hy₁⟩ := h.exists_mem_sec4Y_conj₁
  have hker' : ∀ y : ↥(sec4Y T T₁ T₂), π y = 1 → Sec4ActsTriv T T₁ T₂ (y : G) :=
    fun y hy => (hker y).1 hy
  have hT₁img : (T₁.subgroupOf (sec4Y T T₁ T₂)).map π =
      conjSubgroup (π ⟨y₁, hy₁Y⟩) ((T.subgroupOf (sec4Y T T₁ T₂)).map π) := by
    have := congrArg (fun U : Subgroup G => (U.subgroupOf (sec4Y T T₁ T₂)).map π) hy₁
    rw [this, map_conj_subgroupOf π hy₁Y]
  have hS' : rootGroup S = (T.subgroupOf (sec4Y T T₁ T₂)).map π := hS.symm
  have hS₁ : rootGroup ((π ⟨y₁, hy₁Y⟩) • S) = (T₁.subgroupOf (sec4Y T T₁ T₂)).map π := by
    rw [rootGroup_smul, hT₁img, hS']
  refine ⟨f, P, hP, hfin, π, e, hf, hsurj, hker, S, (π ⟨y₁, hy₁Y⟩) • S, hS, hS₁.symm, ?_⟩
  intro h'
  rw [hS₁] at h'
  have h2 : ((conjSubgroup y₁ T).subgroupOf (sec4Y T T₁ T₂)).map π =
      (T.subgroupOf (sec4Y T T₁ T₂)).map π := by
    have := congrArg (fun U : Subgroup G => (U.subgroupOf (sec4Y T T₁ T₂)).map π) hy₁
    rw [← this, h']
    exact hS'
  have := h.conj_eq_of_map_eq π hker' hy₁Y h2
  exact h.pair.ne (hy₁.trans this)

end PiTwo

section Main

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.exists_normalizing_conj_fix
    (hAsc : AschbacherNoPolarInput) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T)
    (hW : ∀ (f : ℕ) (P : Type) [Group P] [Finite P], 2 ≤ f → (P ≃* PSU3Model f) →
      Lemma21Input P)
    {x : G} (hxT : x ∈ Subgroup.normalizer (T : Set G))
    (hxN : x ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G)) (hxx : x * x = 1)
    (hout : ∀ t ∈ T, ¬ Sec4ActsTriv T T₁ T₂ (x * t)) :
    ∃ w ∈ sec4Y T T₁ T₂, w ∈ Subgroup.normalizer (T : Set G) ∧
      x ∈ Subgroup.normalizer (conjSubgroup w T₁ : Set G) ∧
      (∀ t ∈ T, Sec4ActsTriv T T₁ T₂ (x * t * x⁻¹ * t⁻¹)) ∧
      (∀ s ∈ conjSubgroup w T₁, Sec4ActsTriv T T₁ T₂ (x * s * x⁻¹ * s⁻¹)) ∧
      x ∉ Subgroup.normalizer (conjSubgroup w T₂ : Set G) := by
  obtain ⟨f, P, _, _, π, e, hf, hsurj, hker, S, hS⟩ := h.exists_pi hAsc hq
  have hW' := hW f P hf e
  have hn := h.sec4_three hAsc hq
  have hxY : ∀ y ∈ sec4Y T T₁ T₂, x * y * x⁻¹ ∈ sec4Y T T₁ T₂ := fun y hy => by
    have := hn.conj_mem ⟨y, h.sec4Y_le_normalizer hy⟩ (Subgroup.mem_subgroupOf.2 hy) ⟨x, hxN⟩
    exact Subgroup.mem_subgroupOf.1 this
  obtain ⟨α, hα, hαα⟩ := h.exists_induced_aut π hsurj hker hxx hxY hxN
  have hker' : ∀ y : ↥(sec4Y T T₁ T₂), π y = 1 → Sec4ActsTriv T T₁ T₂ (y : G) :=
    fun y hy => (hker y).1 hy
  set Tt : Subgroup P := (T.subgroupOf (sec4Y T T₁ T₂)).map π with hTt
  have hTtS : rootGroup S = Tt := hS.symm
  have hαT : ∀ z ∈ rootGroup S, α z ∈ rootGroup S := by
    intro z hz
    rw [hTtS] at hz ⊢
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 hz
    rw [hα]
    exact Subgroup.mem_map.2 ⟨⟨x * t' * x⁻¹, hxY _ t'.2⟩, Subgroup.mem_subgroupOf.2
      (conj_mem_of_mem_normalizer hxT (Subgroup.mem_subgroupOf.1 ht')), rfl⟩
  by_cases hin : α ∈ (MulAut.conj : P →* MulAut P).range
  ·
    exfalso
    obtain ⟨tt, htt, hαt⟩ := hW'.inner S α hαα hin hαT
    rw [hTtS] at htt
    obtain ⟨t', ht', hπt'⟩ := Subgroup.mem_map.1 htt
    have htT : (t' : G) ∈ T := Subgroup.mem_subgroupOf.1 ht'
    have htY : (t' : G) ∈ sec4Y T T₁ T₂ := t'.2
    have hux : (t' : G)⁻¹ * x ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G) :=
      (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem
        (h.sec4Y_le_normalizer htY)) hxN
    have huY : ∀ y ∈ sec4Y T T₁ T₂, ((t' : G)⁻¹ * x) * y * ((t' : G)⁻¹ * x)⁻¹ ∈
        sec4Y T T₁ T₂ := by
      intro y hy
      have e1 : ((t' : G)⁻¹ * x) * y * ((t' : G)⁻¹ * x)⁻¹ = (t' : G)⁻¹ * (x * y * x⁻¹) * t' := by
        group
      rw [e1]
      exact (sec4Y T T₁ T₂).mul_mem ((sec4Y T T₁ T₂).mul_mem ((sec4Y T T₁ T₂).inv_mem htY)
        (hxY y hy)) htY
    have hact : Sec4ActsTriv T T₁ T₂ ((t' : G)⁻¹ * x) := by
      refine h.actsTriv_of_pi_conj hq π hker' huY hux fun y => ?_
      have e2 : (⟨((t' : G)⁻¹ * x) * y * ((t' : G)⁻¹ * x)⁻¹, huY y y.2⟩ : ↥(sec4Y T T₁ T₂)) =
          t'⁻¹ * ⟨x * y * x⁻¹, hxY y y.2⟩ * t' := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e2, map_mul, map_mul, map_inv, hπt', ← hα y, hαt]
      simp only [MulAut.conj_apply]
      group
    have ht'' : x⁻¹ * (t' : G)⁻¹ * x ∈ T := by
      have := conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hxT)
        (T.inv_mem htT)
      simpa [mul_assoc] using this
    refine hout _ ht'' ?_
    have e3 : x * (x⁻¹ * (t' : G)⁻¹ * x) = (t' : G)⁻¹ * x := by group
    rw [e3]
    exact hact
  ·
    obtain ⟨hSfix, S', hS'ne, hS'fix⟩ := hW'.outer S α hαα hin hαT
    obtain ⟨y₁, hy₁Y, hy₁⟩ := h.exists_mem_sec4Y_conj₁
    set g₁ : P := π ⟨y₁, hy₁Y⟩ with hg₁
    have hT₁img : (T₁.subgroupOf (sec4Y T T₁ T₂)).map π = conjSubgroup g₁ Tt := by
      have := congrArg (fun U : Subgroup G => (U.subgroupOf (sec4Y T T₁ T₂)).map π) hy₁
      rw [this, map_conj_subgroupOf π hy₁Y]
    have hS₁ : rootGroup (g₁ • S) = (T₁.subgroupOf (sec4Y T T₁ T₂)).map π := by
      rw [rootGroup_smul, hTtS, hT₁img]
    have hS₁ne : rootGroup (g₁ • S) ≠ rootGroup S := by
      intro h'
      rw [hS₁, hTtS] at h'
      have h2 : ((conjSubgroup y₁ T).subgroupOf (sec4Y T T₁ T₂)).map π = Tt := by
        have := congrArg (fun U : Subgroup G => (U.subgroupOf (sec4Y T T₁ T₂)).map π) hy₁
        rw [← this]
        exact h'
      have := h.conj_eq_of_map_eq π hker' hy₁Y h2
      exact h.pair.ne (hy₁.trans this)
    obtain ⟨g, hgN, hg⟩ := hW'.trans S (g₁ • S) S' hS₁ne hS'ne
    obtain ⟨⟨w, hwY⟩, hw₀⟩ := hsurj g
    have hwT : conjSubgroup w T = T := by
      refine h.conj_eq_of_map_eq π hker' hwY ?_
      rw [map_conj_subgroupOf π hwY]
      have h1 : conjSubgroup (π ⟨w, hwY⟩) Tt = Tt := by
        rw [hw₀, ← hTtS]
        exact mem_normalizer_iff_conjSubgroup_eq.1 hgN
      exact h1
    refine ⟨w, hwY, mem_normalizer_of_conjSubgroup_eq hwT, ?_⟩
    set yU : G := w * y₁ with hyU
    have hyUY : yU ∈ sec4Y T T₁ T₂ := (sec4Y T T₁ T₂).mul_mem hwY hy₁Y
    have hU : conjSubgroup w T₁ = conjSubgroup yU T := by
      rw [hy₁, conjSubgroup_conjSubgroup]
    set y' : G := x * yU * x⁻¹ with hy'
    have hy'Y : y' ∈ sec4Y T T₁ T₂ := hxY _ hyUY
    have hxT' : conjSubgroup x T = T := mem_normalizer_iff_conjSubgroup_eq.1 hxT
    have hxU : conjSubgroup x (conjSubgroup yU T) = conjSubgroup y' T := by
      rw [conjSubgroup_conjSubgroup, show x * yU = y' * x by rw [hy']; group,
        ← conjSubgroup_conjSubgroup, hxT']
    set g' : P := π ⟨yU, hyUY⟩ with hg'
    have hg'eq : g' = g * g₁ := by
      rw [hg']
      have : (⟨yU, hyUY⟩ : ↥(sec4Y T T₁ T₂)) = ⟨w, hwY⟩ * ⟨y₁, hy₁Y⟩ := rfl
      rw [this, map_mul, hw₀]
    have hV : conjSubgroup g' Tt = rootGroup S' := by
      rw [hg'eq, ← conjSubgroup_conjSubgroup, ← hTtS, ← rootGroup_smul]
      exact hg
    have hαg' : α g' = π ⟨y', hy'Y⟩ := by
      rw [hg', hα]
    have hmap : ((conjSubgroup y' T).subgroupOf (sec4Y T T₁ T₂)).map π =
        ((conjSubgroup yU T).subgroupOf (sec4Y T T₁ T₂)).map π := by
      rw [map_conj_subgroupOf π hy'Y, map_conj_subgroupOf π hyUY, ← hαg', ← hg', hV]
      have hαα' : ∀ u, α (α u) = u := fun u => by
        have := congrArg (fun m : MulAut P => m u) hαα
        simpa using this
      have hid : ∀ z, α g' * z * (α g')⁻¹ = α (g' * α z * g'⁻¹) := by
        intro z
        simp only [map_mul, map_inv, hαα']
      have hαT' : ∀ z ∈ Tt, α z ∈ Tt := fun z hz => hTtS ▸ hαT z (hTtS ▸ hz)
      have hVmem : ∀ v, v ∈ rootGroup S' ↔ g'⁻¹ * v * g' ∈ Tt := fun v => by
        rw [← hV, mem_conjSubgroup]
      ext v
      rw [mem_conjSubgroup, hVmem]
      constructor
      · intro hz
        set z := (α g')⁻¹ * v * α g' with hzdef
        have hv : v = α g' * z * (α g')⁻¹ := by rw [hzdef]; group
        have hw : g' * α z * g'⁻¹ ∈ rootGroup S' :=
          (hVmem _).2 (by simpa [mul_assoc] using hαT' z hz)
        have hv' : v = g' * α z * g'⁻¹ := by
          rw [hv, hid z]
          exact hS'fix _ hw
        rw [hv']
        simpa [mul_assoc] using hαT' z hz
      · intro hv
        have hv' : v ∈ rootGroup S' := (hVmem v).2 hv
        set z₀ := g'⁻¹ * v * g' with hz₀
        have hv2 : v = g' * z₀ * g'⁻¹ := by rw [hz₀]; group
        have h3 : (α g')⁻¹ * v * α g' = α z₀ := by
          have h4 : α v = α (g' * z₀ * g'⁻¹) := by rw [← hv2]
          rw [hS'fix v hv'] at h4
          simp only [map_mul, map_inv] at h4
          calc (α g')⁻¹ * v * α g' = (α g')⁻¹ * (α g' * α z₀ * (α g')⁻¹) * α g' := by rw [← h4]
            _ = α z₀ := by group
        rw [h3]
        exact hαT' z₀ hv
    have hxeq := h.conj_eq_conj_of_map_eq π hker' hyUY hy'Y hmap
    have hfixT_pi : ∀ (t : G) (ht : t ∈ T), π ⟨x * t * x⁻¹, hxY t (left_le_sec4Y ht)⟩ =
        π ⟨t, left_le_sec4Y ht⟩ := by
      intro t ht
      have hmem : π ⟨t, left_le_sec4Y ht⟩ ∈ rootGroup S := by
        rw [hTtS]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ht)
      have h1 := hSfix _ hmem
      rwa [hα] at h1
    have hfixT₁_pi : ∀ (s : G) (hs : s ∈ conjSubgroup w T₁) (hsY : s ∈ sec4Y T T₁ T₂),
        π ⟨x * s * x⁻¹, hxY s hsY⟩ = π ⟨s, hsY⟩ := by
      intro s hs hsY
      have hs' : s ∈ conjSubgroup yU T := hU ▸ hs
      have hmemV : π ⟨s, hsY⟩ ∈ ((conjSubgroup yU T).subgroupOf (sec4Y T T₁ T₂)).map π :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hs')
      rw [map_conj_subgroupOf π hyUY] at hmemV
      have hmem : π ⟨s, hsY⟩ ∈ rootGroup S' := by
        rw [← hV]
        exact hmemV
      have h1 := hS'fix _ hmem
      rwa [hα] at h1
    have hact : ∀ (u : G) (hu : u ∈ sec4Y T T₁ T₂),
        π ⟨x * u * x⁻¹, hxY u hu⟩ = π ⟨u, hu⟩ → Sec4ActsTriv T T₁ T₂ (x * u * x⁻¹ * u⁻¹) := by
      intro u hu h1
      have hmemY : x * u * x⁻¹ * u⁻¹ ∈ sec4Y T T₁ T₂ :=
        (sec4Y T T₁ T₂).mul_mem (hxY u hu) ((sec4Y T T₁ T₂).inv_mem hu)
      refine (hker ⟨x * u * x⁻¹ * u⁻¹, hmemY⟩).1 ?_
      have e : (⟨x * u * x⁻¹ * u⁻¹, hmemY⟩ : ↥(sec4Y T T₁ T₂)) =
          ⟨x * u * x⁻¹, hxY u hu⟩ * ⟨u, hu⟩⁻¹ := rfl
      rw [e, map_mul, map_inv, h1, mul_inv_cancel]
    refine ⟨mem_normalizer_of_conjSubgroup_eq ?_, fun t ht => hact t _ (hfixT_pi t ht),
      fun s hs => hact s (conjSubgroup_le_sec4Y hyUY (hU ▸ hs))
        (hfixT₁_pi s hs (conjSubgroup_le_sec4Y hyUY (hU ▸ hs))), ?_⟩
    · rw [hU, hxU, hxeq]
    ·
      intro hx₂
      obtain ⟨y₂, hy₂Y, hy₂⟩ := h.exists_mem_sec4Y_conj₂
      have hU₂ : conjSubgroup w T₂ = conjSubgroup (w * y₂) T := by
        rw [hy₂, conjSubgroup_conjSubgroup]
      have hwy₂Y : w * y₂ ∈ sec4Y T T₁ T₂ := (sec4Y T T₁ T₂).mul_mem hwY hy₂Y
      have hS₂ : ((conjSubgroup (w * y₂) T).subgroupOf (sec4Y T T₁ T₂)).map π =
          conjSubgroup (π ⟨w * y₂, hwy₂Y⟩) Tt := map_conj_subgroupOf π hwy₂Y
      have hV₂ : rootGroup (π ⟨w * y₂, hwy₂Y⟩ • S) =
          conjSubgroup (π ⟨w * y₂, hwy₂Y⟩) Tt := by
        rw [rootGroup_smul, hTtS]
      have hαS₂ : ∀ z ∈ rootGroup (π ⟨w * y₂, hwy₂Y⟩ • S),
          α z ∈ rootGroup (π ⟨w * y₂, hwy₂Y⟩ • S) := by
        intro z hz
        rw [hV₂, ← hS₂] at hz ⊢
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hz
        rw [hα]
        refine Subgroup.mem_map.2 ⟨⟨x * u * x⁻¹, hxY _ u.2⟩, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
        have hu' : (u : G) ∈ conjSubgroup (w * y₂) T := Subgroup.mem_subgroupOf.1 hu
        have hx₂' : x ∈ Subgroup.normalizer (conjSubgroup (w * y₂) T : Set G) := hU₂ ▸ hx₂
        exact conj_mem_of_mem_normalizer hx₂' hu'
      obtain ⟨hfix₂, -⟩ := hW'.outer (π ⟨w * y₂, hwy₂Y⟩ • S) α hαα hin hαS₂
      have hfixT₂_pi : ∀ (s : G) (hs : s ∈ conjSubgroup w T₂) (hsY : s ∈ sec4Y T T₁ T₂),
          π ⟨x * s * x⁻¹, hxY s hsY⟩ = π ⟨s, hsY⟩ := by
        intro s hs hsY
        have hs' : s ∈ conjSubgroup (w * y₂) T := hU₂ ▸ hs
        have hmemV : π ⟨s, hsY⟩ ∈
            ((conjSubgroup (w * y₂) T).subgroupOf (sec4Y T T₁ T₂)).map π :=
          Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hs')
        rw [hS₂, ← hV₂] at hmemV
        have h1 := hfix₂ _ hmemV
        rwa [hα] at h1
      have hxX : x ∈ Subgroup.normalizer ((sec4Y T T₁ T₂ : Subgroup G) : Set G) :=
        mem_normalizer_of_conjSubgroup_eq
          (conjSubgroup_eq_of_le (conjSubgroup_le_of_forall_mem hxY))
      let ψ : ↥(sec4Y T T₁ T₂) ≃* ↥(sec4Y T T₁ T₂) :=
        (sec4Y T T₁ T₂).normalizerMonoidHom ⟨x, hxX⟩
      have hψ : ∀ y : ↥(sec4Y T T₁ T₂), ((ψ y : ↥(sec4Y T T₁ T₂)) : G) = x * y * x⁻¹ :=
        fun y => by simp [ψ]
      let Eq : Subgroup ↥(sec4Y T T₁ T₂) := MonoidHom.eqLocus π (π.comp ψ.toMonoidHom)
      have hEq : ∀ (u : G) (hu : u ∈ sec4Y T T₁ T₂),
          π ⟨x * u * x⁻¹, hxY u hu⟩ = π ⟨u, hu⟩ → (⟨u, hu⟩ : ↥(sec4Y T T₁ T₂)) ∈ Eq := by
        intro u hu hh
        show π ⟨u, hu⟩ = π (ψ ⟨u, hu⟩)
        have : ψ ⟨u, hu⟩ = ⟨x * u * x⁻¹, hxY u hu⟩ := Subtype.ext (hψ _)
        rw [this, hh]
      have hYeq : T ⊔ conjSubgroup w T₁ ⊔ conjSubgroup w T₂ = sec4Y T T₁ T₂ :=
        sec4Y_conj_of_mem hwY (mem_normalizer_of_conjSubgroup_eq hwT)
      have hall : ∀ y : ↥(sec4Y T T₁ T₂), y ∈ Eq := by
        rintro ⟨y, hy⟩
        have hy' : y ∈ Subgroup.closure ((T : Set G) ∪ (conjSubgroup w T₁ : Set G) ∪
            (conjSubgroup w T₂ : Set G)) := by
          rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.closure_eq,
            Subgroup.closure_eq, Subgroup.closure_eq, hYeq]
          exact hy
        have hsub : Subgroup.closure ((T : Set G) ∪ (conjSubgroup w T₁ : Set G) ∪
            (conjSubgroup w T₂ : Set G)) ≤ sec4Y T T₁ T₂ := by
          rw [Subgroup.closure_le]
          intro u hu
          rcases hu with (hu | hu) | hu
          · exact left_le_sec4Y hu
          · exact conjSubgroup_le_sec4Y hyUY (hU ▸ hu)
          · exact conjSubgroup_le_sec4Y hwy₂Y (hU₂ ▸ hu)
        refine Subgroup.closure_induction
          (p := fun u hu => ∃ hu' : u ∈ sec4Y T T₁ T₂, (⟨u, hu'⟩ : ↥(sec4Y T T₁ T₂)) ∈ Eq)
          ?_ ?_ ?_ ?_ hy' |>.2
        · intro u hu
          have hu' : u ∈ sec4Y T T₁ T₂ := hsub (Subgroup.subset_closure hu)
          refine ⟨hu', hEq u hu' ?_⟩
          rcases hu with (hu | hu) | hu
          · exact hfixT_pi u hu
          · exact hfixT₁_pi u hu hu'
          · exact hfixT₂_pi u hu hu'
        · exact ⟨(sec4Y T T₁ T₂).one_mem, Eq.one_mem⟩
        · rintro u v hu hv ⟨hu', hEu⟩ ⟨hv', hEv⟩
          exact ⟨(sec4Y T T₁ T₂).mul_mem hu' hv', Eq.mul_mem hEu hEv⟩
        · rintro u hu ⟨hu', hEu⟩
          exact ⟨(sec4Y T T₁ T₂).inv_mem hu', Eq.inv_mem hEu⟩
      have hxact : Sec4ActsTriv T T₁ T₂ x := by
        refine h.actsTriv_of_pi_conj hq π hker' hxY hxN fun y => ?_
        have h1 : π y = π (ψ y) := hall y
        have h2 : ψ y = ⟨x * y * x⁻¹, hxY y y.2⟩ := Subtype.ext (hψ y)
        rw [h2] at h1
        exact h1.symm
      exact hout 1 T.one_mem (by rw [mul_one]; exact hxact)

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.exists_normalizing_conj
    (hAsc : AschbacherNoPolarInput) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T)
    (hW : ∀ (f : ℕ) (P : Type) [Group P] [Finite P], 2 ≤ f → (P ≃* PSU3Model f) →
      Lemma21Input P)
    {x : G} (hxT : x ∈ Subgroup.normalizer (T : Set G))
    (hxN : x ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G)) (hxx : x * x = 1)
    (hout : ∀ t ∈ T, ¬ Sec4ActsTriv T T₁ T₂ (x * t)) :
    ∃ w ∈ sec4Y T T₁ T₂, w ∈ Subgroup.normalizer (T : Set G) ∧
      x ∈ Subgroup.normalizer (conjSubgroup w T₁ : Set G) := by
  obtain ⟨w, hwY, hwT, hxw, -⟩ := h.exists_normalizing_conj_fix hAsc hq hW hxT hxN hxx hout
  exact ⟨w, hwY, hwT, hxw⟩

end Main

end CFSG.CGT.T75B
