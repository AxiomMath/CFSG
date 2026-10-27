module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalIn2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5Struct

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G} {S A B Aa : Subgroup G} {z b : G}

theorem mem_iff_conj_of_mem {S : Subgroup G} {s : G} (hs : s ∈ S) :
    ∀ s', s' ∈ S ↔ s * s' * s⁻¹ ∈ S := fun s' =>
  ⟨fun h => S.mul_mem (S.mul_mem hs h) (S.inv_mem hs), fun h => by
    have := S.mul_mem (S.mul_mem (S.inv_mem hs) h) hs
    simpa [mul_assoc] using this⟩

theorem ThLocalIn.conj_mem_B (W : ThLocalIn L S A B z) {h : G} (hA : ∀ a ∈ A, h⁻¹ * a * h ∈ A)
    (hL : ∀ y ∈ B, h * y * h⁻¹ ∈ L) : ∀ y ∈ B, h * y * h⁻¹ ∈ B := fun y hy => by
  refine (W.mem_B_iff _ (hL y hy)).2 fun a ha => ?_
  have hc := (W.mem_B_iff y (W.B_le hy)).1 hy (h⁻¹ * a * h) (hA a ha)
  calc h * y * h⁻¹ * a = h * (y * (h⁻¹ * a * h)) * h⁻¹ := by group
    _ = h * ((h⁻¹ * a * h) * y) * h⁻¹ := by rw [hc]
    _ = a * (h * y * h⁻¹) := by group

theorem ThLocalIn.B_le_S (W : ThLocalIn L S A B z) : B ≤ S := by
  have hSA : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A := fun s hs a ha =>
    W.conj_mem_A (mem_iff_conj_of_mem hs) ha
  have hSB : ∀ s ∈ S, ∀ y ∈ B, s * y * s⁻¹ ∈ B := fun s hs y hy =>
    W.conj_mem_B (fun a ha => by simpa using hSA s⁻¹ (S.inv_mem hs) a ha)
      (fun y hy => L.mul_mem (L.mul_mem (W.S_le hs) (W.B_le hy)) (L.inv_mem (W.S_le hs))) y hy
  have hB2 : IsPGroup 2 B := IsPGroup.of_card (n := 9) W.B_card
  have hSB' : S ≤ normalizer (B : Set G) := fun s hs =>
    mem_normalizer_iff.2 fun y => ⟨fun hy => hSB s hs y hy, fun hy => by
      have := hSB s⁻¹ (S.inv_mem hs) _ hy
      have e : s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y := by group
      rwa [e] at this⟩
  have hsup : IsPGroup 2 (S ⊔ B : Subgroup G) := W.pgroup.to_sup_of_normal_right' hB2 hSB'
  exact le_sup_right.trans (W.maximal _ (sup_le W.S_le W.B_le) hsup le_sup_left)

theorem ThLocalIn2.conj_mem_of_conj_B (W2 : ThLocalIn2 B A Aa b) {h : G}
    (hB : ∀ y ∈ B, h * y * h⁻¹ ∈ B) : ∀ x ∈ Aa, h * x * h⁻¹ ∈ Aa := by
  have hY : Aa.map (MulAut.conj h).toMonoidHom = Aa := by
    refine W2.Aa_unique _ ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hB x (W2.Aa_le hx)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have := W2.Aa_comm x hx y hy
      calc h * x * h⁻¹ * (h * y * h⁻¹) = h * (x * y) * h⁻¹ := by group
        _ = h * (y * x) * h⁻¹ := by rw [this]
        _ = h * y * h⁻¹ * (h * x * h⁻¹) := by group
    · rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, W2.Aa_card]
  intro x hx
  have : h * x * h⁻¹ ∈ Aa.map (MulAut.conj h).toMonoidHom := ⟨x, hx, by simp⟩
  rwa [hY] at this

section Finite

variable [Finite G]

theorem ThLocalIn2.conj_mem_of_mem_L (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) {n : G}
    (hnL : n ∈ L) (hn : ∀ x ∈ A, n * x * n⁻¹ ∈ A) : ∀ x ∈ Aa, n * x * n⁻¹ ∈ Aa :=
  W2.conj_mem_of_conj_B (W.conj_mem_B (fun _ ha => conj_inv_mem_of_conj_mem hn ha)
    (fun _ hy => L.mul_mem (L.mul_mem hnL (W.B_le hy)) (L.inv_mem hnL)))

theorem ThLocalIn.conj_mem_B_of_normalizes_S (W : ThLocalIn L S A B z) {g : G}
    (hgS : ∀ s, s ∈ S ↔ g * s * g⁻¹ ∈ S) : ∀ y ∈ B, g * y * g⁻¹ ∈ B :=
  W.conj_mem_B (fun _ ha => W.conj_inv_mem_A hgS ha)
    (fun y hy => W.S_le ((hgS y).1 (W.B_le_S hy)))

variable {R : Subgroup G} {t : G}

section Cyc

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)

include H W W2

theorem ThCyc.exists_translation_Aa {g : G} (hgt : g * t * g⁻¹ = z * t)
    (hgS : ∀ s, s ∈ S ↔ g * s * g⁻¹ ∈ S) {a : G} (ha : a ∈ A) :
    ∃ r : G, r * t * r⁻¹ = a * t ∧ (∀ x ∈ A, r * x * r⁻¹ = x) ∧
      ∀ x ∈ Aa, r * x * r⁻¹ ∈ Aa := by
  have hgA' : ∀ x ∈ A, g⁻¹ * x * g ∈ A := fun x hx => W.conj_inv_mem_A hgS hx
  obtain ⟨n, hnL, hn⟩ := W.surj (fun y => g⁻¹ * y * g) (fun x hx => hgA' x hx)
    (fun x hx y hy => by group) (fun x hx y hy hxy => by simpa using hxy)
  have hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A := fun x hx => by rw [hn x hx]; exact hgA' x hx
  have hgAa : ∀ x ∈ Aa, g * x * g⁻¹ ∈ Aa :=
    W2.conj_mem_of_conj_B (W.conj_mem_B_of_normalizes_S hgS)
  have hnAa : ∀ x ∈ Aa, n * x * n⁻¹ ∈ Aa := W2.conj_mem_of_mem_L W hnL hnA
  have hr₀A : ∀ x ∈ A, g * n * x * (g * n)⁻¹ = x := fun x hx => by
    have : g * n * x * (g * n)⁻¹ = g * (n * x * n⁻¹) * g⁻¹ := by group
    rw [this, hn x hx]
    group
  have hnt : n * t * n⁻¹ = t := by
    rw [← H.comm_of_mem_L hnL]
    group
  have hr₀t : g * n * t * (g * n)⁻¹ = z * t := by
    have : g * n * t * (g * n)⁻¹ = g * (n * t * n⁻¹) * g⁻¹ := by group
    rw [this, hnt, hgt]
  have hr₀Aa : ∀ x ∈ Aa, g * n * x * (g * n)⁻¹ ∈ Aa := fun x hx => by
    have : g * n * x * (g * n)⁻¹ = g * (n * x * n⁻¹) * g⁻¹ := by group
    rw [this]
    exact hgAa _ (hnAa x hx)
  by_cases ha1 : a = 1
  · exact ⟨1, by simp [ha1], fun x _ => by simp, fun x hx => by simpa using hx⟩
  · obtain ⟨m, hmL, hmA, hmz⟩ := W.trans a ha ha1
    have hmA' : ∀ x ∈ A, m⁻¹ * x * m ∈ A := fun x hx => conj_inv_mem_of_conj_mem hmA hx
    have hmAa' : ∀ x ∈ Aa, m⁻¹ * x * m ∈ Aa := by
      intro x hx
      have := W2.conj_mem_of_mem_L W (L.inv_mem hmL) (fun x hx => by simpa using hmA' x hx) x hx
      simpa using this
    have hconj : ∀ x : G, m * (g * n) * m⁻¹ * x * (m * (g * n) * m⁻¹)⁻¹ =
        m * ((g * n) * (m⁻¹ * x * m) * (g * n)⁻¹) * m⁻¹ := fun x => by group
    refine ⟨m * (g * n) * m⁻¹, ?_, fun x hx => ?_, fun x hx => ?_⟩
    · have hmt : m * t * m⁻¹ = t := by
        rw [← H.comm_of_mem_L hmL]
        group
      have hmt' : m⁻¹ * t * m = t := by
        rw [← H.comm_of_mem_L (L.inv_mem hmL)]
        group
      calc m * (g * n) * m⁻¹ * t * (m * (g * n) * m⁻¹)⁻¹
          = m * ((g * n) * (m⁻¹ * t * m) * (g * n)⁻¹) * m⁻¹ := by group
        _ = m * (z * t) * m⁻¹ := by rw [hmt', hr₀t]
        _ = (m * z * m⁻¹) * (m * t * m⁻¹) := by group
        _ = a * t := by rw [hmz, hmt]
    · rw [hconj, hr₀A _ (hmA' x hx)]
      group
    · rw [hconj]
      exact W2.conj_mem_of_mem_L W hmL hmA _ (hr₀Aa _ (hmAa' x hx))

theorem ThCyc.conj_mem_Aa_of_centralizes {y : G} (hyA : ∀ a ∈ A, y * a = a * y)
    (hyt : y * t = t * y) : ∀ x ∈ Aa, y * x * y⁻¹ ∈ Aa := by
  have hA : A ≤ L := le_trans (fun x hx => (W.mem_A_iff x).1 hx |>.1) W.S_le
  have hyW : y ∈ centralizer ((W5 A t : Subgroup G) : Set G) := by
    refine mem_centralizer_iff.2 fun w hw => ?_
    rcases (H.mem_W5_iff hA).1 hw with h | ⟨a, ha, rfl⟩
    · exact (hyA w h).symm
    · calc a * t * y = a * (t * y) := by rw [mul_assoc]
        _ = a * (y * t) := by rw [hyt]
        _ = (a * y) * t := by rw [mul_assoc]
        _ = (y * a) * t := by rw [(hyA a ha).symm]
        _ = y * (a * t) := by rw [mul_assoc]
  obtain ⟨b'', hb'', k, rfl⟩ := (H.mem_centralizer_W5_iff W).1 hyW
  intro x hx
  have hxt : t ^ k * x = x * t ^ k :=
    (((show Commute x t from (H.comm_of_mem_L (W.B_le (W2.Aa_le hx))).symm).zpow_right k).eq).symm
  have e : b'' * t ^ k * x * (b'' * t ^ k)⁻¹ = b'' * x * b''⁻¹ := by
    calc b'' * t ^ k * x * (b'' * t ^ k)⁻¹ = b'' * (t ^ k * x) * (t ^ k)⁻¹ * b''⁻¹ := by group
      _ = b'' * (x * t ^ k) * (t ^ k)⁻¹ * b''⁻¹ := by rw [hxt]
      _ = b'' * x * b''⁻¹ := by group
  rw [e]
  exact W2.conj_mem_of_conj_B (fun y hy => B.mul_mem (B.mul_mem hb'' hy) (B.inv_mem hb'')) x hx

theorem ThCyc.Aa_normal {r : G} (hr : r ∈ normalizer ((W5 A t : Subgroup G) : Set G)) :
    ∀ x ∈ Aa, r * x * r⁻¹ ∈ Aa := by
  obtain ⟨P, g, -, -, hgn, -, hgt⟩ := H.exists_fusing_z W
  have hgS := H.normalizes_S W hgn hgt
  obtain ⟨n, hnL, hnA, b', hb', rfl⟩ := H.exists_mul_of_mem_normalizer W hgt hr
  have hnAa := W2.conj_mem_of_mem_L W hnL hnA
  have hθ := H.theta_mem_A W hb'
  obtain ⟨r', hr't, hr'A, hr'Aa⟩ := H.exists_translation_Aa W W2 hgt hgS hθ
  set a₁ := theta t b' with ha₁
  have hb't : b' * t * b'⁻¹ = a₁ * t := by
    rw [ha₁, theta]
    group
  have h1 : r'⁻¹ * a₁ * r' = a₁ := by
    calc r'⁻¹ * a₁ * r' = r'⁻¹ * (r' * a₁ * r'⁻¹) * r' := by rw [hr'A a₁ hθ]
      _ = a₁ := by group
  have h2 : r'⁻¹ * t * r' = a₁⁻¹ * t := by
    calc r'⁻¹ * t * r' = a₁⁻¹ * (a₁ * (r'⁻¹ * t * r')) := by group
      _ = a₁⁻¹ * ((r'⁻¹ * a₁ * r') * (r'⁻¹ * t * r')) := by rw [h1]
      _ = a₁⁻¹ * (r'⁻¹ * (a₁ * t) * r') := by group
      _ = a₁⁻¹ * (r'⁻¹ * (r' * t * r'⁻¹) * r') := by rw [hr't]
      _ = a₁⁻¹ * t := by group
  have hcomm : ∀ a ∈ A, r'⁻¹ * a = a * r'⁻¹ := fun a ha =>
    calc r'⁻¹ * a = r'⁻¹ * (r' * a * r'⁻¹) := by rw [hr'A a ha]
      _ = a * r'⁻¹ := by group
  have hyA : ∀ a ∈ A, (r'⁻¹ * b') * a = a * (r'⁻¹ * b') := fun a ha =>
    calc r'⁻¹ * b' * a = r'⁻¹ * (b' * a) := by rw [mul_assoc]
      _ = r'⁻¹ * (a * b') := by rw [(mem_centralizer_iff.1 hb'.1 a ha).symm]
      _ = (r'⁻¹ * a) * b' := by rw [mul_assoc]
      _ = (a * r'⁻¹) * b' := by rw [hcomm a ha]
      _ = a * (r'⁻¹ * b') := by rw [mul_assoc]
  have hyt : (r'⁻¹ * b') * t = t * (r'⁻¹ * b') := by
    have hconjt : (r'⁻¹ * b') * t * (r'⁻¹ * b')⁻¹ = t := by
      calc (r'⁻¹ * b') * t * (r'⁻¹ * b')⁻¹ = r'⁻¹ * (b' * t * b'⁻¹) * r' := by group
        _ = r'⁻¹ * (a₁ * t) * r' := by rw [hb't]
        _ = (r'⁻¹ * a₁ * r') * (r'⁻¹ * t * r') := by group
        _ = a₁ * (a₁⁻¹ * t) := by rw [h1, h2]
        _ = t := by group
    calc (r'⁻¹ * b') * t = (r'⁻¹ * b') * t * (r'⁻¹ * b')⁻¹ * (r'⁻¹ * b') := by group
      _ = t * (r'⁻¹ * b') := by rw [hconjt]
  have hy := H.conj_mem_Aa_of_centralizes W W2 hyA hyt
  intro x hx
  have e1 : b' * x * b'⁻¹ = r' * (r'⁻¹ * b' * x * (r'⁻¹ * b')⁻¹) * r'⁻¹ := by group
  have e2 : n * b' * x * (n * b')⁻¹ = n * (b' * x * b'⁻¹) * n⁻¹ := by group
  rw [e2, e1]
  exact hnAa _ (hr'Aa _ (hy x hx))

end Cyc

end Finite

end CFSG.EvenSporadicStandard.ThStd
