module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngine3
public import CFSG.Timmesfeld.Bridge.RootSetsModule

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcEngine

open CFSG.Open
open scoped Pointwise

theorem exists_section_lift_of_splits {H G G₀ : Type} [Group H] [Finite H] [Group G] [Group G₀]
    {π : H →* G} (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center H)
    {L : Subgroup G} (hLperf : ⁅L, L⁆ = L) {x : H}
    (hLx : L ≤ Subgroup.centralizer ({π x} : Set G))
    (e : ↥L ≃* G₀)
    {Q : ℕ → Prop} (hQ : ∀ {m n : ℕ}, m ∣ n → Q n → Q m) (hQker : Q (Nat.card π.ker))
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (ρ : E →* G₀), Function.Surjective ρ →
      ρ.ker ≤ Subgroup.center E → Q (Nat.card ρ.ker) →
        ∃ s : G₀ →* E, ∀ g, ρ (s g) = g) :
    ∃ (S : Subgroup H) (eS : ↥S ≃* ↥L),
      S ≤ Subgroup.centralizer ({x} : Set H) ∧ S.map π = L ∧ S ⊓ π.ker = ⊥ ∧
      (∀ s : ↥S, π s = eS s) ∧ Group.IsPerfect ↥S := by
  classical
  let M : Subgroup H := Subgroup.comap π L
  let J' : Subgroup H := ⁅M, M⁆
  have hJ'map : J'.map π = L := by
    dsimp only [J', M]
    exact CFSG.ClassicalInvolution.RouteD.Exotic.map_commutator_comap_eq π hπ hLperf
  have hJ'leC : J' ≤ Subgroup.centralizer ({x} : Set H) := by
    dsimp only [J', M]
    exact CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcEngine.commutator_comap_le_centralizer
      hπ hker hLperf hLx
  let qJ : ↥J' →* ↥L :=
    ((π.comp J'.subtype).codRestrict L (fun y => by
      have hmem : π (y : H) ∈ J'.map π := Subgroup.mem_map_of_mem _ y.2
      rwa [hJ'map] at hmem))
  have hqJ_surj : Function.Surjective qJ := by
    intro j
    have hmem : (j : G) ∈ J'.map π := by rw [hJ'map]; exact j.2
    obtain ⟨y, hy, hπy⟩ := Subgroup.mem_map.mp hmem
    exact ⟨⟨y, hy⟩, Subtype.ext hπy⟩
  let qq : ↥J' →* G₀ := e.toMonoidHom.comp qJ
  have hqq_surj : Function.Surjective qq := fun g => by
    obtain ⟨j, rfl⟩ := e.surjective g
    obtain ⟨y, hy⟩ := hqJ_surj j
    exact ⟨y, by simp [qq, hy]⟩
  have hqq_ker : qq.ker ≤ Subgroup.center ↥J' := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro z
    have hyZ : (y : H) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      have h2 : qJ y = 1 := e.injective (by simpa [qq] using hy)
      exact congrArg Subtype.val h2
    have hycent : (y : H) ∈ Subgroup.center H := hker hyZ
    have hc := (Subgroup.mem_center_iff.mp hycent) (z : H)
    exact Subtype.ext (by simpa using hc)
  have hQqq : Q (Nat.card ↥(qq.ker)) := by
    have hmaple : (qq.ker).map J'.subtype ≤ π.ker := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
      have h1 : qJ y = 1 := e.injective (by simpa [qq] using hy)
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val h1
    have hdvd : Nat.card ↥(qq.ker) ∣ Nat.card ↥(π.ker) := by
      have hcard : Nat.card ↥((qq.ker).map J'.subtype) = Nat.card ↥(qq.ker) :=
        Subgroup.card_map_of_injective J'.subtype_injective
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hmaple
    exact hQ hdvd hQker
  obtain ⟨σ, hσ⟩ := hsplit ↥J' qq hqq_surj hqq_ker hQqq
  let S : Subgroup H := σ.range.map J'.subtype
  have hqJσ : ∀ g, qJ (σ g) = e.symm g := by
    intro g
    apply e.injective
    have := hσ g
    simpa [qq] using this
  have hSker : S ⊓ π.ker = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    obtain ⟨hsS, hsk⟩ := Subgroup.mem_inf.mp hs
    obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.mp hsS
    obtain ⟨g, hg⟩ := hy
    have hsEq : s = J'.subtype (σ g) := by
      calc s = J'.subtype y := hys.symm
        _ = J'.subtype (σ g) := by rw [← hg]
    have h1 : π (J'.subtype (σ g)) = 1 := hsEq ▸ hsk
    have h2 : qJ (σ g) = 1 := Subtype.ext (by
      change π (J'.subtype (σ g)) = 1
      exact h1)
    have h3 : e.symm g = 1 := by rw [← hqJσ g, h2]
    have h4 : g = 1 := by simpa using congrArg e h3
    have hy1 : y = 1 := by rw [← hg]; simp [h4]
    calc s = J'.subtype y := hys.symm
      _ = J'.subtype 1 := by rw [hy1]
      _ = 1 := by simp
  let eSfun : ↥S →* ↥L :=
    { toFun := fun s => ⟨π (s : H), by
        obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.mp s.2
        obtain ⟨g, hg⟩ := hy
        have hEq : J'.subtype (σ g) = s := by rw [hg, hys]
        rw [← hEq]
        exact (qJ (σ g)).2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [map_mul]) }
  have heSfun_inj : Function.Injective eSfun := by
    intro a b hab
    have hπ : π (a : H) = π (b : H) := congrArg Subtype.val hab
    have hmemS : (a : H)⁻¹ * (b : H) ∈ S := S.mul_mem (S.inv_mem a.2) b.2
    have hmemker : (a : H)⁻¹ * (b : H) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπ, inv_mul_cancel]
    have hinf : (a : H)⁻¹ * (b : H) ∈ S ⊓ π.ker := ⟨hmemS, hmemker⟩
    rw [hSker] at hinf
    have h1 : (a : H)⁻¹ * (b : H) = 1 := Subgroup.mem_bot.mp hinf
    have h2 : (b : H) = (a : H) := by
      have := congrArg (fun z => (a : H) * z) h1
      simpa [mul_assoc] using this
    exact Subtype.ext h2.symm
  have heSfun_surj : Function.Surjective eSfun := by
    intro j
    refine ⟨⟨J'.subtype (σ (e j)), ⟨σ (e j), ⟨e j, rfl⟩, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change (qJ (σ (e j)) : G) = ((j : ↥L) : G)
    have h := congrArg (fun z : ↥L => (z : G)) (hqJσ (e j))
    rw [show e.symm (e j) = j from MulEquiv.symm_apply_apply e j] at h
    exact h
  let eS : ↥S ≃* ↥L := MulEquiv.ofBijective eSfun ⟨heSfun_inj, heSfun_surj⟩
  have hSleC : S ≤ Subgroup.centralizer ({x} : Set H) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hJ'leC y.2
  have hSmap : S.map π = L := by
    apply le_antisymm
    · rintro _ ⟨s, hs, rfl⟩
      exact (eSfun ⟨s, hs⟩).2
    · intro j hj
      obtain ⟨s, hs⟩ := heSfun_surj ⟨j, hj⟩
      exact ⟨s, s.2, congrArg Subtype.val hs⟩
  have hSπ : ∀ s : ↥S, π s = eS s := fun s => rfl
  have hSperf : Group.IsPerfect ↥S := by
    letI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLperf
    exact Group.IsPerfect.ofSurjective (f := eS.symm.toMonoidHom) eS.symm.surjective
  exact ⟨S, eS, hSleC, hSmap, hSker, hSπ, hSperf⟩

theorem commute_of_sections_of_central_cover {H G : Type} [Group H] [Group G]
    {π : H →* G} (hker : π.ker ≤ Subgroup.center H)
    {J J₁ : Subgroup G} {S S₁ : Subgroup H}
    (hSJ : ∀ a ∈ S, π a ∈ J) (hS₁J₁ : ∀ b ∈ S₁, π b ∈ J₁)
    (hcomm : ∀ a ∈ J, ∀ b ∈ J₁, Commute a b) (hSperf : ⁅S, S⁆ = S) :
    ∀ a ∈ S, ∀ b ∈ S₁, Commute a b := by
  intro a ha b hb
  refine CFSG.Timmesfeld.Bridge.commute_of_perfect hSperf ?_ ?_ a ha
  · intro a ha c hc
    have hz : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      have hc' := hcomm (π a) (hSJ a ha) (π b) (hS₁J₁ b hb)
      simp only [map_mul, map_inv]
      rw [hc'.eq]
      group
    exact (Subgroup.mem_center_iff.mp (hker hz) c).symm
  · intro a ha c hc
    have hza : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      have hc' := hcomm (π a) (hSJ a ha) (π b) (hS₁J₁ b hb)
      simp only [map_mul, map_inv]
      rw [hc'.eq]
      group
    have hzc : c * b * c⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      have hc' := hcomm (π c) (hSJ c hc) (π b) (hS₁J₁ b hb)
      simp only [map_mul, map_inv]
      rw [hc'.eq]
      group
    exact (Subgroup.mem_center_iff.mp (hker hza) _).symm

private theorem exists_qTorus_lift {H G : Type} [Group H] [Group G]
    {π : H →* G} {J : Subgroup G} {S : Subgroup H} (eS : ↥S ≃* ↥J)
    (hSπ : ∀ s : ↥S, π s = eS s) {q : ℕ} {F₀ : Subgroup G}
    (hF₀le : F₀ ≤ J) (hF₀el : IsElemAbelian q F₀) (hF₀card : Nat.card F₀ = q ^ 2) :
    ∃ T : Subgroup H, T ≤ S ∧ IsElemAbelian q T ∧ Nat.card T = q ^ 2 ∧ T.map π = F₀ := by
  let T : Subgroup H := ((F₀.subgroupOf J).map eS.symm.toMonoidHom).map S.subtype
  have hTcard : Nat.card T = q ^ 2 := by
    rw [Subgroup.card_map_of_injective S.subtype_injective,
      Subgroup.card_map_of_injective eS.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF₀le).toEquiv, hF₀card]
  have hTel : IsElemAbelian q T :=
    IsElemAbelian.map (IsElemAbelian.map (hF₀el.subgroupOf J) eS.symm.toMonoidHom) S.subtype
  have hcomp : π.comp S.subtype = J.subtype.comp eS.toMonoidHom := by
    ext s
    exact hSπ s
  have hTmap : T.map π = F₀ := by
    have hsub : ((F₀.subgroupOf J).map eS.symm.toMonoidHom).map eS.toMonoidHom =
        F₀.subgroupOf J := by
      rw [Subgroup.map_map]
      have hid : eS.toMonoidHom.comp eS.symm.toMonoidHom = MonoidHom.id ↥J := by
        ext x
        simp
      rw [hid, Subgroup.map_id]
    have hTm : T.map π =
        ((F₀.subgroupOf J).map eS.symm.toMonoidHom).map (π.comp S.subtype) := by
      rw [Subgroup.map_map]
    calc T.map π =
        ((F₀.subgroupOf J).map eS.symm.toMonoidHom).map (π.comp S.subtype) := hTm
      _ = ((F₀.subgroupOf J).map eS.symm.toMonoidHom).map
            (J.subtype.comp eS.toMonoidHom) := by rw [hcomp]
      _ = (((F₀.subgroupOf J).map eS.symm.toMonoidHom).map eS.toMonoidHom).map
            J.subtype :=
          (Subgroup.map_map ((F₀.subgroupOf J).map eS.symm.toMonoidHom) J.subtype
            eS.toMonoidHom).symm
      _ = (F₀.subgroupOf J).map J.subtype := by rw [hsub]
      _ = F₀ := Subgroup.map_subgroupOf_eq_of_le hF₀le
  exact ⟨T, Subgroup.map_subtype_le _, hTel, hTcard, hTmap⟩

private theorem exists_qElement_of_noncentral {H G : Type} [Group H] [Group G]
    {π : H →* G} (hker : π.ker ≤ Subgroup.center H)
    {J J₁ : Subgroup G} {S S₁ : Subgroup H} (eS : ↥S ≃* ↥J) (eS₁ : ↥S₁ ≃* ↥J₁)
    (hSπ : ∀ a : ↥S, π a = eS a) (hS₁π : ∀ b : ↥S₁, π b = eS₁ b)
    (hcomm : ∀ a ∈ J, ∀ b ∈ J₁, Commute a b) (hSperf : ⁅S, S⁆ = S)
    {q : ℕ} (hq : q.Prime) {s₀ : G} (hs₀J₁ : s₀ ∈ J₁) (hs₀q : orderOf s₀ = q)
    (hs₀Z : (⟨s₀, hs₀J₁⟩ : ↥J₁) ∉ Subgroup.center ↥J₁) :
    ∃ y₁ : H, y₁ ∈ S₁ ∧ orderOf y₁ = q ∧ π y₁ = s₀ ∧ y₁ ∉ S := by
  have hSJ : ∀ a ∈ S, π a ∈ J := fun a ha => by
    rw [hSπ ⟨a, ha⟩]
    exact (eS ⟨a, ha⟩).2
  have hS₁J₁ : ∀ b ∈ S₁, π b ∈ J₁ := fun b hb => by
    rw [hS₁π ⟨b, hb⟩]
    exact (eS₁ ⟨b, hb⟩).2
  have hSS₁ : ∀ a ∈ S, ∀ b ∈ S₁, Commute a b :=
    commute_of_sections_of_central_cover hker hSJ hS₁J₁ hcomm hSperf
  let y₁ : ↥S₁ := eS₁.symm ⟨s₀, hs₀J₁⟩
  have hy₁q : orderOf (y₁ : H) = q := by
    have h1 : orderOf y₁ = orderOf (⟨s₀, hs₀J₁⟩ : ↥J₁) := by
      show orderOf (eS₁.symm ⟨s₀, hs₀J₁⟩) = orderOf (⟨s₀, hs₀J₁⟩ : ↥J₁)
      exact MulEquiv.orderOf_eq eS₁.symm _
    rw [Subgroup.orderOf_coe, h1, ← Subgroup.orderOf_coe]
    exact hs₀q
  have hy₁π : π (y₁ : H) = s₀ := by
    have h := hS₁π y₁
    simpa [y₁] using h
  have hy₁notS : (y₁ : H) ∉ S := by
    intro hyS
    apply hs₀Z
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨b', rfl⟩ := eS₁.surjective b
    have hb : y₁ * b' = b' * y₁ := Subtype.ext (hSS₁ (y₁ : H) hyS b' b'.2).eq
    simpa [y₁, map_mul] using (congrArg eS₁ hb).symm
  exact ⟨(y₁ : H), y₁.2, hy₁q, hy₁π, hy₁notS⟩

private theorem exists_elemAbelian_card_pow_three_of_sections {H G : Type} [Group H] [Finite H]
    [Group G] [Finite G] {π : H →* G} (hker : π.ker ≤ Subgroup.center H)
    {x : H} {J J₁ : Subgroup G} {S S₁ : Subgroup H}
    (eS : ↥S ≃* ↥J) (eS₁ : ↥S₁ ≃* ↥J₁)
    (hSleC : S ≤ Subgroup.centralizer ({x} : Set H))
    (hS₁leC : S₁ ≤ Subgroup.centralizer ({x} : Set H))
    (hSπ : ∀ a : ↥S, π a = eS a) (hS₁π : ∀ b : ↥S₁, π b = eS₁ b)
    (hSperf : ⁅S, S⁆ = S) (hcomm : ∀ a ∈ J, ∀ b ∈ J₁, Commute a b)
    {q : ℕ} (hq : q.Prime) {F₀ : Subgroup G} (hF₀le : F₀ ≤ J)
    (hF₀el : IsElemAbelian q F₀) (hF₀card : Nat.card F₀ = q ^ 2)
    {s₀ : G} (hs₀J₁ : s₀ ∈ J₁) (hs₀q : orderOf s₀ = q)
    (hs₀Z : (⟨s₀, hs₀J₁⟩ : ↥J₁) ∉ Subgroup.center ↥J₁) :
    ∃ F : Subgroup H, IsElemAbelian q F ∧ Nat.card F = q ^ 3 ∧
      F ≤ Subgroup.centralizer ({x} : Set H) ∧
      F.map π = F₀ ⊔ Subgroup.zpowers s₀ ∧
      F.map π ≤ Subgroup.normalizer (J : Set G) ∧
      F ⊓ π.ker = ⊥ ∧ 3 ≤ CFSG.Open.pRank q F := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨y₁, hy₁S₁, hy₁q, hy₁π, hy₁notS⟩ :=
    exists_qElement_of_noncentral hker eS eS₁ hSπ hS₁π hcomm hSperf hq hs₀J₁ hs₀q hs₀Z
  obtain ⟨T, hTleS, hTel, hTcard, hTmap⟩ :=
    exists_qTorus_lift eS hSπ hF₀le hF₀el hF₀card
  have hSJ : ∀ a ∈ S, π a ∈ J := fun a ha => by
    rw [hSπ ⟨a, ha⟩]
    exact (eS ⟨a, ha⟩).2
  have hS₁J₁ : ∀ b ∈ S₁, π b ∈ J₁ := fun b hb => by
    rw [hS₁π ⟨b, hb⟩]
    exact (eS₁ ⟨b, hb⟩).2
  have hSS₁ : ∀ a ∈ S, ∀ b ∈ S₁, Commute a b :=
    commute_of_sections_of_central_cover hker hSJ hS₁J₁ hcomm hSperf
  set F : Subgroup H := T ⊔ Subgroup.zpowers y₁ with hFdef
  have hy₁el : IsElemAbelian q (Subgroup.zpowers y₁) :=
    isElemAbelian_zpowers (by rw [← hy₁q]; exact pow_orderOf_eq_one y₁)
  have hcommT : ∀ a ∈ T, ∀ b ∈ Subgroup.zpowers y₁, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hcommS : Commute a y₁ := hSS₁ a (hTleS ha) y₁ hy₁S₁
    rw [← hk]
    exact (hcommS.zpow_right k).eq
  have hFel : IsElemAbelian q F := by
    rw [hFdef]
    exact IsElemAbelian.sup_of_commute hTel hy₁el hcommT
  have hy₁1 : y₁ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy₁q
    exact hq.ne_one hy₁q.symm
  have hTinf : T ⊓ Subgroup.zpowers y₁ = ⊥ := by
    rw [inf_comm]
    exact CFSG.zpowers_inf_eq_bot_of_not_mem hq
      (by rw [← hy₁q]; exact pow_orderOf_eq_one y₁) hy₁1
      (fun h => hy₁notS (hTleS h))
  have hFcard : Nat.card F = q ^ 3 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute T
      (Subgroup.zpowers y₁) hcommT).1
    rw [hTinf, Subgroup.card_bot, hTcard, Nat.card_zpowers, hy₁q, mul_one] at h
    rw [hFdef, h]
    ring
  have hFx : F ≤ Subgroup.centralizer ({x} : Set H) := by
    rw [hFdef]
    refine sup_le ?_ ?_
    · exact hTleS.trans hSleC
    · exact Subgroup.zpowers_le.mpr (hS₁leC hy₁S₁)
  have hFmap : F.map π = F₀ ⊔ Subgroup.zpowers s₀ := by
    rw [hFdef, Subgroup.map_sup, hTmap]
    congr 1
    rw [MonoidHom.map_zpowers, hy₁π]
  have hs₀1 : s₀ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs₀q
    exact hq.ne_one hs₀q.symm
  have hs₀F₀ : s₀ ∉ F₀ := by
    intro hs
    apply hs₀Z
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext (hcomm s₀ (hF₀le hs) b b.2).eq.symm
  have hF0s₀ : F₀ ⊓ Subgroup.zpowers s₀ = ⊥ := by
    rw [inf_comm]
    exact CFSG.zpowers_inf_eq_bot_of_not_mem hq
      (by rw [← hs₀q]; exact pow_orderOf_eq_one s₀) hs₀1 hs₀F₀
  have hFsupcard : Nat.card (F₀ ⊔ Subgroup.zpowers s₀ : Subgroup G) = q ^ 3 := by
    have hcomm' : ∀ a ∈ F₀, ∀ b ∈ Subgroup.zpowers s₀, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← hk]
      exact ((hcomm a (hF₀le ha) s₀ hs₀J₁).zpow_right k).eq
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute F₀
      (Subgroup.zpowers s₀) hcomm').1
    rw [hF0s₀, Subgroup.card_bot, hF₀card, Nat.card_zpowers, hs₀q, mul_one] at h
    rw [h]
    ring
  have hFZ : F ⊓ π.ker = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyF, hyker⟩ := Subgroup.mem_inf.mp hy
    have hrange : Nat.card ↥((π.comp F.subtype).range) = Nat.card ↥F := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hFmap, hFsupcard, hFcard]
    have hmul := Subgroup.card_ker_mul_card_range (π.comp F.subtype)
    rw [hrange] at hmul
    have hker1 : Nat.card ↥((π.comp F.subtype).ker) = 1 := by
      have hmul' : Nat.card ↥((π.comp F.subtype).ker) * Nat.card ↥F = 1 * Nat.card ↥F := by
        rw [hmul, one_mul]
      exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) hmul'
    have hkerbot : ((π.comp F.subtype).ker = ⊥) := Subgroup.card_eq_one.mp hker1
    have hy' : (⟨y, hyF⟩ : ↥F) ∈ ((π.comp F.subtype).ker) := by
      rw [MonoidHom.mem_ker]
      simpa using hyker
    have hy1 : (⟨y, hyF⟩ : ↥F) = 1 := Subgroup.mem_bot.mp (hkerbot ▸ hy')
    exact Subtype.ext_iff.mp hy1
  have hFJ : F.map π ≤ Subgroup.normalizer (J : Set G) := by
    rw [hFmap]
    refine sup_le ?_ ?_
    · exact hF₀le.trans Subgroup.le_normalizer
    · refine (Subgroup.zpowers_le.mpr ?_).trans
        (Subgroup.centralizer_le_normalizer (J : Set G))
      exact Subgroup.mem_centralizer_iff.mpr (fun j hj => (hcomm j hj s₀ hs₀J₁).eq)
  have hF3 : 3 ≤ CFSG.Open.pRank q F :=
    CFSG.SectionRank.le_pRank hq.one_lt le_rfl hFel (by rw [hFcard])
  exact ⟨F, hFel, hFcard, hFx, hFmap, hFJ, hFZ, hF3⟩

theorem concl165Avoid_of_sections {H G : Type} [Group H] [Finite H] [Group G] [Finite G]
    {π : H →* G} (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center H)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {Ã : Subgroup H} (hÃ : IsElemAbelian p Ã)
    {x z : H} (hxÃ : x ∈ Ã) (hzÃ : z ∈ Ã) (hx1 : x ≠ 1) (hzx : z ∉ Subgroup.zpowers x)
    {J J₁ Q : Subgroup G}
    (hJx : J ≤ Subgroup.centralizer ({π x} : Set G))
    (hJn : (J.subgroupOf (Subgroup.centralizer ({π x} : Set G))).Normal)
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card J)
    (hQJ : Q ≤ J) (hQz : Q ≤ Subgroup.centralizer ({π z} : Set G))
    (hQn : (Q.subgroupOf (J ⊓ Subgroup.centralizer ({π z} : Set G))).Normal)
    (hQq : CFSG.Open.IsQuasisimple ↥Q) (hpQ : p ∣ Nat.card Q)
    {S S₁ : Subgroup H} (eS : ↥S ≃* ↥J) (eS₁ : ↥S₁ ≃* ↥J₁)
    (hSleC : S ≤ Subgroup.centralizer ({x} : Set H))
    (hS₁leC : S₁ ≤ Subgroup.centralizer ({x} : Set H))
    (hSπ : ∀ a : ↥S, π a = eS a) (hS₁π : ∀ b : ↥S₁, π b = eS₁ b)
    (hSker : S ⊓ π.ker = ⊥) (hS₁ker : S₁ ⊓ π.ker = ⊥)
    (hcomm : ∀ a ∈ J, ∀ b ∈ J₁, Commute a b)
    {F₀ : Subgroup G} (hF₀le : F₀ ≤ J) (hF₀el : IsElemAbelian q F₀)
    (hF₀card : Nat.card F₀ = q ^ 2) {s₀ : G} (hs₀J₁ : s₀ ∈ J₁) (hs₀q : orderOf s₀ = q)
    (hs₀Z : (⟨s₀, hs₀J₁⟩ : ↥J₁) ∉ Subgroup.center ↥J₁) :
    Concl165Avoid H p q Ã π.ker := by
  classical
  haveI : Group.IsPerfect ↥J := Group.IsPerfect.mk hJq.1
  have hSperf : ⁅S, S⁆ = S :=
    (Subgroup.isPerfect_iff (H := S)).mp
      (Group.IsPerfect.ofSurjective (f := eS.symm.toMonoidHom) eS.symm.surjective)
  obtain ⟨F, hFel, hFcard, hFx, hFmap, hFJ, hFZ, hF3⟩ :=
    exists_elemAbelian_card_pow_three_of_sections hker eS eS₁ hSleC hS₁leC hSπ hS₁π
      hSperf hcomm hq hF₀le hF₀el hF₀card hs₀J₁ hs₀q hs₀Z
  exact concl165Avoid_of_central_lift hp π hπ hker hÃ hxÃ hzÃ hx1 hzx hJx hJn hJq hpJ
    hQJ hQz hQn hQq hpQ hFel hFx hFJ hF3 hFZ

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcEngine
